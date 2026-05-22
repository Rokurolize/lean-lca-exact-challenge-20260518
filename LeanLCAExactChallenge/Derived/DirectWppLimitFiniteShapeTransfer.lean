import LeanLCAExactChallenge.LCA.Pullback
import LeanLCAExactChallenge.Derived.DirectWppOpColimitFiniteShapeTransfer

/-!
WPP limit stability as a finite-shape transfer input.

This module records the direct route from a cochain-level WPP limit comparison and
exact-acyclic WPP limit closure to the `WalkingParallelPair` limit-stability field
used by the `Dbounded` finite-shape transfer constructor.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace DirectWppLimitFiniteShapeTransfer

/-- The direct bounded exact weak-equivalence property for default-universe metrizable LCAs. -/
abbrev directWeakEquivalence :
    MorphismProperty (BoundedComplexCategory MetrizableLCA.{0}) :=
  boundedExactWeakEquivalence MetrizableLCA.{0}

/-- Direct WPP limit stability for bounded exact weak equivalences. -/
abbrev DirectWalkingParallelPairLimitStability : Prop :=
  directWeakEquivalence.IsStableUnderLimitsOfShape WalkingParallelPair

/-- Constructor-level condition for direct WPP limit stability. -/
abbrev DirectWalkingParallelPairLimitCondition : Prop :=
  ∀ (X₁ X₂ : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0})
    (c₁ : Cone X₁) (c₂ : Cone X₂)
    (_ : IsLimit c₁) (_ : IsLimit c₂) (f : X₁ ⟶ X₂),
      directWeakEquivalence.functorCategory WalkingParallelPair f →
        ∀ (φ : c₁.pt ⟶ c₂.pt),
          (∀ j : WalkingParallelPair,
            φ ≫ c₂.π.app j = c₁.π.app j ≫ f.app j) →
              directWeakEquivalence φ

/-- Mapping-cone comparison input for WPP limit comparison maps. -/
abbrev mappingCone_boundedInclusion_walkingParallelPair_limitComparison : Prop :=
  ∀ (X₁ X₂ : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0})
    (c₁ : Cone X₁) (c₂ : Cone X₂)
    (_ : IsLimit c₁) (_ : IsLimit c₂) (f : X₁ ⟶ X₂),
      directWeakEquivalence.functorCategory WalkingParallelPair f →
        ∀ (φ : c₁.pt ⟶ c₂.pt),
          (∀ j : WalkingParallelPair,
            φ ≫ c₂.π.app j = c₁.π.app j ≫ f.app j) →
            ∃ (K : WalkingParallelPair ⥤ CochainComplex MetrizableLCA.{0} ℤ)
              (ck : Cone K),
                Nonempty (IsLimit ck) ∧
                  (∀ j : WalkingParallelPair,
                    exactAcyclic MetrizableLCA (K.obj j)) ∧
                  Nonempty
                    (CochainComplex.mappingCone
                        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ) ≅ ck.pt)

/-- Fixed-diagram limit-cone comparison input for WPP mapping cones. -/
abbrev mappingCone_walkingParallelPair_limitConeComparison : Prop :=
  ∀ (X₁ X₂ : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0})
    (c₁ : Cone X₁) (c₂ : Cone X₂)
    (_ : IsLimit c₁) (_ : IsLimit c₂) (f : X₁ ⟶ X₂)
    (φ : c₁.pt ⟶ c₂.pt),
      (∀ j : WalkingParallelPair,
        φ ≫ c₂.π.app j = c₁.π.app j ≫ f.app j) →
          ∃ (ck : Cone
            (WppOpMappingConeUniqueMediatorW308.mappingConeDiagram X₁ X₂ f)),
              Nonempty (IsLimit ck) ∧
                Nonempty
                  (CochainComplex.mappingCone
                      ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ) ≅ ck.pt)

/-- The fixed mapping-cone diagram comparison supplies the full WPP comparison input. -/
theorem mappingCone_boundedInclusion_walkingParallelPair_limitComparison_of_limitConeComparison
    (hcomparison : mappingCone_walkingParallelPair_limitConeComparison) :
    mappingCone_boundedInclusion_walkingParallelPair_limitComparison := by
  intro X₁ X₂ c₁ c₂ hc₁ hc₂ f hf φ hφ
  rcases hcomparison X₁ X₂ c₁ c₂ hc₁ hc₂ f φ hφ with
    ⟨ck, hck, hiso⟩
  refine
    ⟨WppOpMappingConeUniqueMediatorW308.mappingConeDiagram X₁ X₂ f, ck, hck, ?_, hiso⟩
  intro j
  exact hf j

/-- The canonical mapping-cone cone induced by compatible WPP limit cones. -/
noncomputable def mappingConeCone {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (c₁ : Cone X₁) (c₂ : Cone X₂) (f : X₁ ⟶ X₂)
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j : J, φ ≫ c₂.π.app j = c₁.π.app j ≫ f.app j) :
    Cone (WppOpMappingConeUniqueMediatorW308.mappingConeDiagram X₁ X₂ f) where
  pt :=
    CochainComplex.mappingCone
      ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)
  π :=
    { app := fun j =>
        CochainComplex.mappingCone.map
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₁.π.app j))
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₂.π.app j))
          (by
            rw [← Functor.map_comp, ← Functor.map_comp]
            exact congrArg
              (fun g => (BoundedComplexCategory.ι MetrizableLCA.{0}).map g)
              (hφ j))
      naturality := by
        intro j j' α
        dsimp [WppOpMappingConeUniqueMediatorW308.mappingConeDiagram]
        rw [← CochainComplex.mappingCone.map_comp]
        simp only [Category.id_comp]
        symm
        congr 2
        · exact congrArg (fun g => g.hom) (c₁.w α)
        · exact congrArg (fun g => g.hom) (c₂.w α) }

/-- Projection of `mappingCone.map` to the shifted source summand. -/
@[reassoc]
lemma mappingCone_map_f_fst {K₁ L₁ K₂ L₂ : CochainComplex MetrizableLCA.{0} ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂)
    (n : ℤ) :
    (CochainComplex.mappingCone.map φ₁ φ₂ a b comm).f n ≫
        (CochainComplex.mappingCone.fst φ₂).1.v n (n + 1) rfl =
      (CochainComplex.mappingCone.fst φ₁).1.v n (n + 1) rfl ≫ a.f (n + 1) := by
  unfold CochainComplex.mappingCone.map
  rw [CochainComplex.mappingCone.desc_f _ _ _ _ n (n + 1) rfl]
  simp [Category.assoc]

/-- Precomposed projection of `mappingCone.map` to the shifted source summand. -/
lemma comp_mappingCone_map_f_fst {K₁ L₁ K₂ L₂ : CochainComplex MetrizableLCA.{0} ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂)
    (n : ℤ) {Z : MetrizableLCA.{0}} (g : Z ⟶ (CochainComplex.mappingCone φ₁).X n) :
    g ≫ (CochainComplex.mappingCone.map φ₁ φ₂ a b comm).f n ≫
        (CochainComplex.mappingCone.fst φ₂).1.v n (n + 1) rfl =
      g ≫ (CochainComplex.mappingCone.fst φ₁).1.v n (n + 1) rfl ≫ a.f (n + 1) := by
  rw [mappingCone_map_f_fst]

/-- Projection of `mappingCone.map` to the target summand. -/
@[reassoc]
lemma mappingCone_map_f_snd {K₁ L₁ K₂ L₂ : CochainComplex MetrizableLCA.{0} ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂)
    (n : ℤ) :
    (CochainComplex.mappingCone.map φ₁ φ₂ a b comm).f n ≫
        (CochainComplex.mappingCone.snd φ₂).v n n (add_zero n) =
      (CochainComplex.mappingCone.snd φ₁).v n n (add_zero n) ≫ b.f n := by
  unfold CochainComplex.mappingCone.map
  rw [CochainComplex.mappingCone.desc_f _ _ _ _ n (n + 1) rfl]
  simp [Category.assoc]

/-- Precomposed projection of `mappingCone.map` to the target summand. -/
lemma comp_mappingCone_map_f_snd {K₁ L₁ K₂ L₂ : CochainComplex MetrizableLCA.{0} ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂)
    (n : ℤ) {Z : MetrizableLCA.{0}} (g : Z ⟶ (CochainComplex.mappingCone φ₁).X n) :
    g ≫ (CochainComplex.mappingCone.map φ₁ φ₂ a b comm).f n ≫
        (CochainComplex.mappingCone.snd φ₂).v n n (add_zero n) =
      g ≫ (CochainComplex.mappingCone.snd φ₁).v n n (add_zero n) ≫ b.f n := by
  rw [mappingCone_map_f_snd]

/-- Recombining mapping-cone source and target components then projecting by `fst`. -/
lemma mappingCone_inl_inr_fst {K L : CochainComplex MetrizableLCA.{0} ℤ}
    (φ : K ⟶ L) (n : ℤ) {Z : MetrizableLCA.{0}}
    (a : Z ⟶ K.X (n + 1)) (b : Z ⟶ L.X n) :
    (a ≫ (CochainComplex.mappingCone.inl φ).v (n + 1) n (by omega) +
        b ≫ (CochainComplex.mappingCone.inr φ).f n) ≫
      (CochainComplex.mappingCone.fst φ).1.v n (n + 1) rfl = a := by
  rw [Preadditive.add_comp]
  simp [Category.assoc]

/-- Recombining mapping-cone source and target components then projecting by `snd`. -/
lemma mappingCone_inl_inr_snd {K L : CochainComplex MetrizableLCA.{0} ℤ}
    (φ : K ⟶ L) (n : ℤ) {Z : MetrizableLCA.{0}}
    (a : Z ⟶ K.X (n + 1)) (b : Z ⟶ L.X n) :
    (a ≫ (CochainComplex.mappingCone.inl φ).v (n + 1) n (by omega) +
        b ≫ (CochainComplex.mappingCone.inr φ).f n) ≫
      (CochainComplex.mappingCone.snd φ).v n n (add_zero n) = b := by
  rw [Preadditive.add_comp]
  simp [Category.assoc]

/-- The canonical cone leg projected to the shifted source summand. -/
lemma comp_mappingConeCone_π_fst {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (c₁ : Cone X₁) (c₂ : Cone X₂) (f : X₁ ⟶ X₂)
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j : J, φ ≫ c₂.π.app j = c₁.π.app j ≫ f.app j)
    (j : J) (n : ℤ) {Z : MetrizableLCA.{0}}
    (g : Z ⟶
      (CochainComplex.mappingCone
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)).X n) :
    g ≫ ((mappingConeCone c₁ c₂ f φ hφ).π.app j).f n ≫
        (CochainComplex.mappingCone.fst
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))).1.v
            n (n + 1) rfl =
      g ≫
        (CochainComplex.mappingCone.fst
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)).1.v
            n (n + 1) rfl ≫
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₁.π.app j)).f (n + 1) := by
  simpa [mappingConeCone] using
    comp_mappingCone_map_f_fst
      ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)
      ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))
      ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₁.π.app j))
      ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₂.π.app j))
      (by
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg
          (fun q => (BoundedComplexCategory.ι MetrizableLCA.{0}).map q)
          (hφ j))
      n g

/-- The canonical cone leg projected to the target summand. -/
lemma comp_mappingConeCone_π_snd {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (c₁ : Cone X₁) (c₂ : Cone X₂) (f : X₁ ⟶ X₂)
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j : J, φ ≫ c₂.π.app j = c₁.π.app j ≫ f.app j)
    (j : J) (n : ℤ) {Z : MetrizableLCA.{0}}
    (g : Z ⟶
      (CochainComplex.mappingCone
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)).X n) :
    g ≫ ((mappingConeCone c₁ c₂ f φ hφ).π.app j).f n ≫
        (CochainComplex.mappingCone.snd
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))).v
            n n (add_zero n) =
      g ≫
        (CochainComplex.mappingCone.snd
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)).v
            n n (add_zero n) ≫
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₂.π.app j)).f n := by
  simpa [mappingConeCone] using
    comp_mappingCone_map_f_snd
      ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)
      ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))
      ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₁.π.app j))
      ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₂.π.app j))
      (by
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg
          (fun q => (BoundedComplexCategory.ι MetrizableLCA.{0}).map q)
          (hφ j))
      n g

/-- Source projection cone associated to a degreewise test cone over the WPP mapping-cone diagram. -/
noncomputable def mappingConeDegreewiseSourceCone
    {X₁ X₂ : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (f : X₁ ⟶ X₂) (n : ℤ)
    (s : Cone (WppOpMappingConeUniqueMediatorW308.mappingConeDiagram X₁ X₂ f ⋙
      HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) n)) :
    Cone (X₁ ⋙ BoundedComplexCategory.ι MetrizableLCA.{0} ⋙
      HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) (n + 1)) where
  pt := s.pt
  π :=
    { app := fun j =>
        s.π.app j ≫
          (CochainComplex.mappingCone.fst
            ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))).1.v
              n (n + 1) rfl
      naturality := by
        intro j j' α
        dsimp [WppOpMappingConeUniqueMediatorW308.mappingConeDiagram]
        symm
        have hmap :
            (CochainComplex.mappingCone.map
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j'))
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₁.map α))
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₂.map α))
                (by
                  rw [← Functor.map_comp, ← Functor.map_comp]
                  exact congrArg
                    (fun q => (BoundedComplexCategory.ι MetrizableLCA.{0}).map q)
                    (f.naturality α).symm)).f n ≫
              (CochainComplex.mappingCone.fst
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j'))).1.v
                  n (n + 1) rfl =
            (CochainComplex.mappingCone.fst
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))).1.v
                  n (n + 1) rfl ≫
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₁.map α)).f
                (n + 1) := by
          exact mappingCone_map_f_fst _ _ _ _ _ n
        calc
          (s.π.app j ≫
              (CochainComplex.mappingCone.fst
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))).1.v
                  n (n + 1) rfl) ≫
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₁.map α)).f
                (n + 1) =
            s.π.app j ≫
              ((CochainComplex.mappingCone.map
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j'))
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₁.map α))
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₂.map α))
                (by
                  rw [← Functor.map_comp, ← Functor.map_comp]
                  exact congrArg
                    (fun q => (BoundedComplexCategory.ι MetrizableLCA.{0}).map q)
                    (f.naturality α).symm)).f n ≫
              (CochainComplex.mappingCone.fst
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j'))).1.v
                  n (n + 1) rfl) := by
              simpa [Category.assoc] using congrArg (fun q => s.π.app j ≫ q) hmap.symm
          _ = (s.π.app j ≫
              (CochainComplex.mappingCone.map
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j'))
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₁.map α))
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₂.map α))
                (by
                  rw [← Functor.map_comp, ← Functor.map_comp]
                  exact congrArg
                    (fun q => (BoundedComplexCategory.ι MetrizableLCA.{0}).map q)
                    (f.naturality α).symm)).f n) ≫
              (CochainComplex.mappingCone.fst
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j'))).1.v
                  n (n + 1) rfl := by simp [Category.assoc]
          _ = s.π.app j' ≫
              (CochainComplex.mappingCone.fst
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j'))).1.v
                  n (n + 1) rfl := by
              simpa [WppOpMappingConeUniqueMediatorW308.mappingConeDiagram, Category.assoc]
                using congrArg
                  (fun q => q ≫
                    (CochainComplex.mappingCone.fst
                      ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j'))).1.v
                        n (n + 1) rfl) (s.w α) }

/-- Target projection cone associated to a degreewise test cone over the WPP mapping-cone diagram. -/
noncomputable def mappingConeDegreewiseTargetCone
    {X₁ X₂ : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (f : X₁ ⟶ X₂) (n : ℤ)
    (s : Cone (WppOpMappingConeUniqueMediatorW308.mappingConeDiagram X₁ X₂ f ⋙
      HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) n)) :
    Cone (X₂ ⋙ BoundedComplexCategory.ι MetrizableLCA.{0} ⋙
      HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) n) where
  pt := s.pt
  π :=
    { app := fun j =>
        s.π.app j ≫
          (CochainComplex.mappingCone.snd
            ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))).v
              n n (add_zero n)
      naturality := by
        intro j j' α
        dsimp [WppOpMappingConeUniqueMediatorW308.mappingConeDiagram]
        symm
        have hmap :
            (CochainComplex.mappingCone.map
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j'))
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₁.map α))
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₂.map α))
                (by
                  rw [← Functor.map_comp, ← Functor.map_comp]
                  exact congrArg
                    (fun q => (BoundedComplexCategory.ι MetrizableLCA.{0}).map q)
                    (f.naturality α).symm)).f n ≫
              (CochainComplex.mappingCone.snd
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j'))).v
                  n n (add_zero n) =
            (CochainComplex.mappingCone.snd
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))).v
                  n n (add_zero n) ≫
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₂.map α)).f n := by
          exact mappingCone_map_f_snd _ _ _ _ _ n
        calc
          (s.π.app j ≫
              (CochainComplex.mappingCone.snd
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))).v
                  n n (add_zero n)) ≫
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₂.map α)).f n =
            s.π.app j ≫
              ((CochainComplex.mappingCone.map
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j'))
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₁.map α))
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₂.map α))
                (by
                  rw [← Functor.map_comp, ← Functor.map_comp]
                  exact congrArg
                    (fun q => (BoundedComplexCategory.ι MetrizableLCA.{0}).map q)
                    (f.naturality α).symm)).f n ≫
              (CochainComplex.mappingCone.snd
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j'))).v
                  n n (add_zero n)) := by
              simpa [Category.assoc] using congrArg (fun q => s.π.app j ≫ q) hmap.symm
          _ = (s.π.app j ≫
              (CochainComplex.mappingCone.map
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j'))
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₁.map α))
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₂.map α))
                (by
                  rw [← Functor.map_comp, ← Functor.map_comp]
                  exact congrArg
                    (fun q => (BoundedComplexCategory.ι MetrizableLCA.{0}).map q)
                    (f.naturality α).symm)).f n) ≫
              (CochainComplex.mappingCone.snd
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j'))).v
                  n n (add_zero n) := by simp [Category.assoc]
          _ = s.π.app j' ≫
              (CochainComplex.mappingCone.snd
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j'))).v
                  n n (add_zero n) := by
              simpa [WppOpMappingConeUniqueMediatorW308.mappingConeDiagram, Category.assoc]
                using congrArg
                  (fun q => q ≫
                    (CochainComplex.mappingCone.snd
                      ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j'))).v
                        n n (add_zero n)) (s.w α) }

/-- Canonical-cone limit input for WPP mapping-cone comparison. -/
abbrev mappingCone_walkingParallelPair_limitCanonicalConeComparison : Prop :=
  ∀ (X₁ X₂ : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0})
    (c₁ : Cone X₁) (c₂ : Cone X₂)
    (_ : IsLimit c₁) (_ : IsLimit c₂) (f : X₁ ⟶ X₂)
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j : WalkingParallelPair,
      φ ≫ c₂.π.app j = c₁.π.app j ≫ f.app j),
      Nonempty (IsLimit (mappingConeCone c₁ c₂ f φ hφ))

/-- Degreewise limit input for the canonical WPP mapping-cone cone. -/
abbrev mappingCone_walkingParallelPair_limitCanonicalConeDegreewiseComparison : Prop :=
  ∀ (X₁ X₂ : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0})
    (c₁ : Cone X₁) (c₂ : Cone X₂)
    (_ : IsLimit c₁) (_ : IsLimit c₂) (f : X₁ ⟶ X₂)
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j : WalkingParallelPair,
      φ ≫ c₂.π.app j = c₁.π.app j ≫ f.app j)
    (n : ℤ),
      Nonempty (IsLimit
        ((HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) n).mapCone
          (mappingConeCone c₁ c₂ f φ hφ)))

/-- Direct degreewise limit proof for the canonical WPP mapping-cone cone. -/
theorem mappingCone_walkingParallelPair_limitCanonicalConeDegreewiseComparison_direct :
    mappingCone_walkingParallelPair_limitCanonicalConeDegreewiseComparison := by
  intro X₁ X₂ c₁ c₂ hc₁ hc₂ f φ hφ n
  let φc := (BoundedComplexCategory.ι MetrizableLCA.{0}).map φ
  let inlφ := (CochainComplex.mappingCone.inl φc).v (n + 1) n (by omega)
  let inrφ := (CochainComplex.mappingCone.inr φc).f n
  let fstφ := (CochainComplex.mappingCone.fst φc).1.v n (n + 1) rfl
  let sndφ := (CochainComplex.mappingCone.snd φc).v n n (add_zero n)
  have hc₁n : IsLimit
      ((HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) (n + 1)).mapCone
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).mapCone c₁)) := by
    exact isLimitOfPreserves
      (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) (n + 1))
      (isLimitOfPreserves (BoundedComplexCategory.ι MetrizableLCA.{0}) hc₁)
  have hc₂n : IsLimit
      ((HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) n).mapCone
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).mapCone c₂)) := by
    exact isLimitOfPreserves (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) n)
      (isLimitOfPreserves (BoundedComplexCategory.ι MetrizableLCA.{0}) hc₂)
  refine ⟨?_⟩
  refine
    { lift := fun s =>
        let a : s.pt ⟶ ((BoundedComplexCategory.ι MetrizableLCA.{0}).obj c₁.pt).X (n + 1) :=
          hc₁n.lift (mappingConeDegreewiseSourceCone f n s)
        let b : s.pt ⟶ ((BoundedComplexCategory.ι MetrizableLCA.{0}).obj c₂.pt).X n :=
          hc₂n.lift (mappingConeDegreewiseTargetCone f n s)
        a ≫ inlφ + b ≫ inrφ
      fac := ?_
      uniq := ?_ }
  · intro s j
    let a : s.pt ⟶ ((BoundedComplexCategory.ι MetrizableLCA.{0}).obj c₁.pt).X (n + 1) :=
      hc₁n.lift (mappingConeDegreewiseSourceCone f n s)
    let b : s.pt ⟶ ((BoundedComplexCategory.ι MetrizableLCA.{0}).obj c₂.pt).X n :=
      hc₂n.lift (mappingConeDegreewiseTargetCone f n s)
    have hfst : (a ≫ inlφ + b ≫ inrφ) ≫ fstφ = a := by
      simpa [φc, inlφ, inrφ, fstφ] using mappingCone_inl_inr_fst φc n a b
    have hsnd : (a ≫ inlφ + b ≫ inrφ) ≫ sndφ = b := by
      simpa [φc, inlφ, inrφ, sndφ] using mappingCone_inl_inr_snd φc n a b
    apply CochainComplex.mappingCone.ext_to
      ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) n (n + 1) rfl
    · calc
        ((a ≫ inlφ + b ≫ inrφ) ≫
            ((mappingConeCone c₁ c₂ f φ hφ).π.app j).f n) ≫
            (CochainComplex.mappingCone.fst
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))).1.v
                n (n + 1) rfl =
          (a ≫ inlφ + b ≫ inrφ) ≫
            fstφ ≫
            ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₁.π.app j)).f (n + 1) := by
            simpa [Category.assoc, φc, fstφ] using
              comp_mappingConeCone_π_fst c₁ c₂ f φ hφ j n
                (g := a ≫ inlφ + b ≫ inrφ)
        _ = a ≫ ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₁.π.app j)).f
              (n + 1) := by
            rw [← Category.assoc, hfst]
        _ = s.π.app j ≫
            (CochainComplex.mappingCone.fst
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))).1.v
                n (n + 1) rfl := by
            simpa [a, mappingConeDegreewiseSourceCone] using
              hc₁n.fac (mappingConeDegreewiseSourceCone f n s) j
    · calc
        ((a ≫ inlφ + b ≫ inrφ) ≫
            ((mappingConeCone c₁ c₂ f φ hφ).π.app j).f n) ≫
            (CochainComplex.mappingCone.snd
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))).v
                n n (add_zero n) =
          (a ≫ inlφ + b ≫ inrφ) ≫
            sndφ ≫
            ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₂.π.app j)).f n := by
            simpa [Category.assoc, φc, sndφ] using
              comp_mappingConeCone_π_snd c₁ c₂ f φ hφ j n
                (g := a ≫ inlφ + b ≫ inrφ)
        _ = b ≫ ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₂.π.app j)).f n := by
            rw [← Category.assoc, hsnd]
        _ = s.π.app j ≫
            (CochainComplex.mappingCone.snd
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))).v
                n n (add_zero n) := by
            simpa [b, mappingConeDegreewiseTargetCone] using
              hc₂n.fac (mappingConeDegreewiseTargetCone f n s) j
  · intro s m hm
    let a : s.pt ⟶ ((BoundedComplexCategory.ι MetrizableLCA.{0}).obj c₁.pt).X (n + 1) :=
      hc₁n.lift (mappingConeDegreewiseSourceCone f n s)
    let b : s.pt ⟶ ((BoundedComplexCategory.ι MetrizableLCA.{0}).obj c₂.pt).X n :=
      hc₂n.lift (mappingConeDegreewiseTargetCone f n s)
    have hfst : (a ≫ inlφ + b ≫ inrφ) ≫ fstφ = a := by
      simpa [φc, inlφ, inrφ, fstφ] using mappingCone_inl_inr_fst φc n a b
    have hsnd : (a ≫ inlφ + b ≫ inrφ) ≫ sndφ = b := by
      simpa [φc, inlφ, inrφ, sndφ] using mappingCone_inl_inr_snd φc n a b
    apply CochainComplex.mappingCone.ext_to φc n (n + 1) rfl
    · have hm₁ : m ≫ fstφ = a := by
        dsimp [a]
        apply hc₁n.uniq (mappingConeDegreewiseSourceCone f n s)
        intro j
        calc
          (m ≫ fstφ) ≫
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₁.π.app j)).f
                (n + 1) =
            m ≫ ((mappingConeCone c₁ c₂ f φ hφ).π.app j).f n ≫
              (CochainComplex.mappingCone.fst
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))).1.v
                  n (n + 1) rfl := by
              simpa [Category.assoc, φc, fstφ] using
                (comp_mappingConeCone_π_fst c₁ c₂ f φ hφ j n (g := m)).symm
          _ = s.π.app j ≫
              (CochainComplex.mappingCone.fst
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))).1.v
                  n (n + 1) rfl := by
              simpa [Category.assoc] using congrArg
                (fun q => q ≫
                  (CochainComplex.mappingCone.fst
                    ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))).1.v
                      n (n + 1) rfl) (hm j)
      calc
        m ≫ fstφ = a := hm₁
        _ = (a ≫ inlφ + b ≫ inrφ) ≫ fstφ := hfst.symm
    · have hm₂ : m ≫ sndφ = b := by
        dsimp [b]
        apply hc₂n.uniq (mappingConeDegreewiseTargetCone f n s)
        intro j
        calc
          (m ≫ sndφ) ≫
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₂.π.app j)).f n =
            m ≫ ((mappingConeCone c₁ c₂ f φ hφ).π.app j).f n ≫
              (CochainComplex.mappingCone.snd
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))).v
                  n n (add_zero n) := by
              simpa [Category.assoc, φc, sndφ] using
                (comp_mappingConeCone_π_snd c₁ c₂ f φ hφ j n (g := m)).symm
          _ = s.π.app j ≫
              (CochainComplex.mappingCone.snd
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))).v
                  n n (add_zero n) := by
              simpa [Category.assoc] using congrArg
                (fun q => q ≫
                  (CochainComplex.mappingCone.snd
                    ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))).v
                      n n (add_zero n)) (hm j)
      calc
        m ≫ sndφ = b := hm₂
        _ = (a ≫ inlφ + b ≫ inrφ) ≫ sndφ := hsnd.symm

/-- Degreewise limit proofs supply the canonical mapping-cone cone limit input. -/
theorem mappingCone_walkingParallelPair_limitCanonicalConeComparison_of_degreewise
    (hcomparison : mappingCone_walkingParallelPair_limitCanonicalConeDegreewiseComparison) :
    mappingCone_walkingParallelPair_limitCanonicalConeComparison := by
  intro X₁ X₂ c₁ c₂ hc₁ hc₂ f φ hφ
  exact ⟨HomologicalComplex.isLimitOfEval _ _ (fun n =>
    Classical.choice (hcomparison X₁ X₂ c₁ c₂ hc₁ hc₂ f φ hφ n))⟩

/-- A limit proof for the canonical cone supplies the WPP cone-comparison input. -/
theorem mappingCone_walkingParallelPair_limitConeComparison_of_canonicalCone
    (hcomparison : mappingCone_walkingParallelPair_limitCanonicalConeComparison) :
    mappingCone_walkingParallelPair_limitConeComparison := by
  intro X₁ X₂ c₁ c₂ hc₁ hc₂ f φ hφ
  refine ⟨mappingConeCone c₁ c₂ f φ hφ, ?_, ?_⟩
  · exact hcomparison X₁ X₂ c₁ c₂ hc₁ hc₂ f φ hφ
  · exact ⟨Iso.refl _⟩

/-- The W551 direct degreewise proof supplies the canonical cone comparison input. -/
theorem mappingCone_walkingParallelPair_limitCanonicalConeComparison_direct :
    mappingCone_walkingParallelPair_limitCanonicalConeComparison :=
  mappingCone_walkingParallelPair_limitCanonicalConeComparison_of_degreewise
    mappingCone_walkingParallelPair_limitCanonicalConeDegreewiseComparison_direct

/-- The W551 direct proof supplies the fixed mapping-cone diagram cone comparison input. -/
theorem mappingCone_walkingParallelPair_limitConeComparison_direct :
    mappingCone_walkingParallelPair_limitConeComparison :=
  mappingCone_walkingParallelPair_limitConeComparison_of_canonicalCone
    mappingCone_walkingParallelPair_limitCanonicalConeComparison_direct

/-- The W551 direct proof supplies the full WPP mapping-cone comparison input. -/
theorem mappingCone_boundedInclusion_walkingParallelPair_limitComparison_direct :
    mappingCone_boundedInclusion_walkingParallelPair_limitComparison :=
  mappingCone_boundedInclusion_walkingParallelPair_limitComparison_of_limitConeComparison
    mappingCone_walkingParallelPair_limitConeComparison_direct

/-- Exact-acyclic WPP limit closure input for cochain complexes. -/
abbrev exactAcyclic_metrizableLCA_walkingParallelPair_limitClosure : Prop :=
  ∀ (K : WalkingParallelPair ⥤ CochainComplex MetrizableLCA.{0} ℤ)
    (ck : Cone K),
      IsLimit ck →
        (∀ j : WalkingParallelPair, exactAcyclic MetrizableLCA (K.obj j)) →
          exactAcyclic MetrizableLCA ck.pt

/-- The degreewise short-complex functor for cochain complexes over `MetrizableLCA`. -/
abbrev degreeShortComplexFunctor (i : ℤ) :
    CochainComplex MetrizableLCA.{0} ℤ ⥤ ShortComplex MetrizableLCA.{0} :=
  HomologicalComplex.shortComplexFunctor MetrizableLCA.{0} (ComplexShape.up ℤ) i

/-- WPP limits preserve the left closed-embedding field of strict short complexes. -/
abbrev wppLimit_preserves_leftClosedEmbedding : Prop :=
  ∀ (S : WalkingParallelPair ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cone S),
      IsLimit cs →
        (∀ j : WalkingParallelPair,
          IsClosedEmbedding ((S.obj j).f : (S.obj j).X₁ → (S.obj j).X₂)) →
          IsClosedEmbedding (cs.pt.f : cs.pt.X₁ → cs.pt.X₂)

/--
Pure component-level LCA certificate for the left closed-embedding WPP limit field.
For the induced map between WPP limit points it is enough to prove injectivity,
induced source topology, and closed image.
-/
abbrev wppLimit_lca_limitMap_injective_inducing_closedImage : Prop :=
  ∀ (X Y : WalkingParallelPair ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cone X) (cy : Cone Y) (φ : cx.pt ⟶ cy.pt),
      IsLimit cx →
        IsLimit cy →
          (∀ j : WalkingParallelPair,
            IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
            (∀ j : WalkingParallelPair, φ ≫ cy.π.app j = cx.π.app j ≫ α.app j) →
              Function.Injective (φ : cx.pt → cy.pt) ∧
                IsInducing (φ : cx.pt → cy.pt) ∧
                  IsClosed (Set.range (φ : cx.pt → cy.pt))

/-- A limiting WPP cone gives a limiting fork on the two parallel arrows. -/
def forkOfConeIsLimit {C : Type*} [Category C] {F : WalkingParallelPair ⥤ C}
    {c : Cone F} (hc : IsLimit c) : IsLimit (Fork.ofCone c) :=
  Fork.IsLimit.mk (Fork.ofCone c)
    (fun s => hc.lift (Cone.ofFork s))
    (fun s => by
      change hc.lift (Cone.ofFork s) ≫
          (Fork.ofCone c).π.app WalkingParallelPair.zero =
        s.π.app WalkingParallelPair.zero
      simpa [Fork.ofCone, Cone.ofFork] using
        (hc.fac (Cone.ofFork s) WalkingParallelPair.zero))
    (fun s m hm => by
      have hfac0 :
          hc.lift (Cone.ofFork s) ≫ c.π.app WalkingParallelPair.zero =
            s.π.app WalkingParallelPair.zero := by
        simpa [Fork.ofCone, Cone.ofFork] using
          (hc.fac (Cone.ofFork s) WalkingParallelPair.zero)
      have hm0 : m ≫ c.π.app WalkingParallelPair.zero = s.π.app WalkingParallelPair.zero := by
        have hm0' : m ≫ (Fork.ofCone c).π.app WalkingParallelPair.zero =
            s.π.app WalkingParallelPair.zero := by
          change m ≫ (Fork.ofCone c).ι = s.ι
          exact hm
        simpa [Fork.ofCone] using hm0'
      apply hc.hom_ext
      intro j
      rcases j with (_ | _)
      · change m ≫ c.π.app WalkingParallelPair.zero =
          hc.lift (Cone.ofFork s) ≫ c.π.app WalkingParallelPair.zero
        rw [hm0, hfac0]
      · have hzero : m ≫ c.π.app WalkingParallelPair.zero =
            hc.lift (Cone.ofFork s) ≫ c.π.app WalkingParallelPair.zero := by
          change m ≫ c.π.app WalkingParallelPair.zero =
            hc.lift (Cone.ofFork s) ≫ c.π.app WalkingParallelPair.zero
          rw [hm0, hfac0]
        calc
          m ≫ c.π.app WalkingParallelPair.one =
              (m ≫ c.π.app WalkingParallelPair.zero) ≫
                F.map WalkingParallelPairHom.left := by
                rw [Category.assoc]
                exact congrArg (fun q => m ≫ q)
                  (c.w WalkingParallelPairHom.left).symm
          _ = (hc.lift (Cone.ofFork s) ≫ c.π.app WalkingParallelPair.zero) ≫
              F.map WalkingParallelPairHom.left := by
                exact congrArg (fun q => q ≫ F.map WalkingParallelPairHom.left) hzero
          _ = hc.lift (Cone.ofFork s) ≫
              (c.π.app WalkingParallelPair.zero ≫ F.map WalkingParallelPairHom.left) := by
                rw [Category.assoc]
          _ = hc.lift (Cone.ofFork s) ≫ c.π.app WalkingParallelPair.one := by
                exact congrArg (fun q => hc.lift (Cone.ofFork s) ≫ q)
                  (c.w WalkingParallelPairHom.left))

/-- The zero projection of a limiting WPP cone in `MetrizableLCA` is a closed embedding. -/
theorem walkingParallelPair_limit_π_zero_closedEmbedding
    {F : WalkingParallelPair ⥤ MetrizableLCA.{0}} {c : Cone F}
    (hc : IsLimit c) :
    IsClosedEmbedding (c.π.app WalkingParallelPair.zero : c.pt → F.obj WalkingParallelPair.zero) := by
  have hfork : IsLimit (Fork.ofCone c) := forkOfConeIsLimit hc
  have hclosed := MetrizableLCA.isLimit_fork_ι_closedEmbedding
    (F.map WalkingParallelPairHom.left) (F.map WalkingParallelPairHom.right) hfork
  simpa [Fork.ofCone] using hclosed

/-- Direct WPP limit certificate for preserving closed embeddings on induced maps. -/
theorem wppLimit_lca_limitMap_injective_inducing_closedImage_direct :
    wppLimit_lca_limitMap_injective_inducing_closedImage := by
  intro X Y α cx cy φ hcx hcy hclosed hφ
  let πx₀ : cx.pt ⟶ X.obj WalkingParallelPair.zero := cx.π.app WalkingParallelPair.zero
  let πy₀ : cy.pt ⟶ Y.obj WalkingParallelPair.zero := cy.π.app WalkingParallelPair.zero
  have hπx₀ : IsClosedEmbedding (πx₀ : cx.pt → X.obj WalkingParallelPair.zero) := by
    simpa [πx₀] using walkingParallelPair_limit_π_zero_closedEmbedding (F := X) hcx
  have hπy₀ : IsClosedEmbedding (πy₀ : cy.pt → Y.obj WalkingParallelPair.zero) := by
    simpa [πy₀] using walkingParallelPair_limit_π_zero_closedEmbedding (F := Y) hcy
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    apply hπx₀.injective
    apply (hclosed WalkingParallelPair.zero).injective
    calc
      (α.app WalkingParallelPair.zero) (πx₀ a) = πy₀ (φ a) := by
        exact (congrArg (fun h : cx.pt ⟶ Y.obj WalkingParallelPair.zero => h a)
          (hφ WalkingParallelPair.zero)).symm
      _ = πy₀ (φ b) := by rw [hab]
      _ = (α.app WalkingParallelPair.zero) (πx₀ b) := by
        exact congrArg (fun h : cx.pt ⟶ Y.obj WalkingParallelPair.zero => h b)
          (hφ WalkingParallelPair.zero)
  · have hcomp_fun :
        ((πy₀ : cy.pt → Y.obj WalkingParallelPair.zero) ∘ (φ : cx.pt → cy.pt)) =
          ((α.app WalkingParallelPair.zero : X.obj WalkingParallelPair.zero →
              Y.obj WalkingParallelPair.zero) ∘
            (πx₀ : cx.pt → X.obj WalkingParallelPair.zero)) := by
      funext x
      exact congrArg (fun h : cx.pt ⟶ Y.obj WalkingParallelPair.zero => h x)
        (hφ WalkingParallelPair.zero)
    have hcomp_ind :
        IsInducing
          ((πy₀ : cy.pt → Y.obj WalkingParallelPair.zero) ∘ (φ : cx.pt → cy.pt)) := by
      rw [hcomp_fun]
      exact (hclosed WalkingParallelPair.zero).toIsEmbedding.toIsInducing.comp
        hπx₀.toIsEmbedding.toIsInducing
    exact hπy₀.toIsEmbedding.toIsInducing.of_comp_iff.mp hcomp_ind
  · have hrange :
        Set.range (φ : cx.pt → cy.pt) =
          (πy₀ : cy.pt → Y.obj WalkingParallelPair.zero) ⁻¹'
            Set.range (α.app WalkingParallelPair.zero :
              X.obj WalkingParallelPair.zero → Y.obj WalkingParallelPair.zero) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        refine ⟨πx₀ x, ?_⟩
        exact (congrArg (fun h : cx.pt ⟶ Y.obj WalkingParallelPair.zero => h x)
          (hφ WalkingParallelPair.zero)).symm
      · rintro ⟨x₀, hx₀⟩
        have hx_eq :
            (X.map WalkingParallelPairHom.left) x₀ =
              (X.map WalkingParallelPairHom.right) x₀ := by
          apply (hclosed WalkingParallelPair.one).injective
          calc
            (α.app WalkingParallelPair.one)
                ((X.map WalkingParallelPairHom.left) x₀) =
              (Y.map WalkingParallelPairHom.left)
                ((α.app WalkingParallelPair.zero) x₀) := by
                exact congrArg
                  (fun h : X.obj WalkingParallelPair.zero ⟶
                      Y.obj WalkingParallelPair.one => h x₀)
                  (α.naturality WalkingParallelPairHom.left)
            _ = (Y.map WalkingParallelPairHom.left) (πy₀ y) := by rw [hx₀]
            _ = (cy.π.app WalkingParallelPair.one) y := by
              exact congrArg
                (fun h : cy.pt ⟶ Y.obj WalkingParallelPair.one => h y)
                (cy.w WalkingParallelPairHom.left)
            _ = (Y.map WalkingParallelPairHom.right) (πy₀ y) := by
              exact (congrArg
                (fun h : cy.pt ⟶ Y.obj WalkingParallelPair.one => h y)
                (cy.w WalkingParallelPairHom.right)).symm
            _ = (Y.map WalkingParallelPairHom.right)
                ((α.app WalkingParallelPair.zero) x₀) := by rw [hx₀]
            _ = (α.app WalkingParallelPair.one)
                ((X.map WalkingParallelPairHom.right) x₀) := by
                exact (congrArg
                  (fun h : X.obj WalkingParallelPair.zero ⟶
                      Y.obj WalkingParallelPair.one => h x₀)
                  (α.naturality WalkingParallelPairHom.right)).symm
        let z : MetrizableLCA.equalizerObj
            (X.map WalkingParallelPairHom.left) (X.map WalkingParallelPairHom.right) :=
          ⟨x₀, hx_eq⟩
        let fx : Fork (X.map WalkingParallelPairHom.left) (X.map WalkingParallelPairHom.right) :=
          Fork.ofCone cx
        have hfx : IsLimit fx := by
          simpa [fx] using forkOfConeIsLimit hcx
        let ex := IsLimit.conePointUniqueUpToIso hfx
          (MetrizableLCA.equalizerIsLimit
            (X.map WalkingParallelPairHom.left) (X.map WalkingParallelPairHom.right))
        let x : cx.pt := ex.inv z
        have hex_inv :
            ex.inv ≫ (Fork.ofCone cx).ι =
              MetrizableLCA.equalizerι
                (X.map WalkingParallelPairHom.left) (X.map WalkingParallelPairHom.right) := by
          simpa [ex] using
            (IsLimit.conePointUniqueUpToIso_inv_comp hfx
              (MetrizableLCA.equalizerIsLimit
                (X.map WalkingParallelPairHom.left) (X.map WalkingParallelPairHom.right))
              WalkingParallelPair.zero)
        have hxπ : πx₀ x = x₀ := by
          change (ex.inv ≫ (Fork.ofCone cx).ι) z = x₀
          rw [hex_inv]
          rfl
        refine ⟨x, ?_⟩
        apply hπy₀.injective
        calc
          πy₀ (φ x) = (α.app WalkingParallelPair.zero) (πx₀ x) := by
            exact congrArg (fun h : cx.pt ⟶ Y.obj WalkingParallelPair.zero => h x)
              (hφ WalkingParallelPair.zero)
          _ = (α.app WalkingParallelPair.zero) x₀ := by rw [hxπ]
          _ = πy₀ y := hx₀
    rw [hrange]
    exact (hclosed WalkingParallelPair.zero).isClosed_range.preimage πy₀.hom.continuous

/-- The three-part topological certificate is exactly enough for a closed embedding. -/
theorem closedEmbedding_of_injective_inducing_closedImage
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (hinj : Function.Injective f) (hind : IsInducing f)
    (hclosed : IsClosed (Set.range f)) :
    IsClosedEmbedding f :=
  { toIsEmbedding := { toIsInducing := hind, injective := hinj }
    isClosed_range := hclosed }

/-- The pure LCA certificate supplies the WPP limit left closed-embedding field. -/
theorem wppLimit_preserves_leftClosedEmbedding_of_injective_inducing_closedImage
    (hlimit : wppLimit_lca_limitMap_injective_inducing_closedImage) :
    wppLimit_preserves_leftClosedEmbedding := by
  intro S cs hcs hclosed
  let α : S ⋙ (ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤
      MetrizableLCA.{0}) ⟶
      S ⋙ (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤
        MetrizableLCA.{0}) :=
    { app := fun j => (S.obj j).f
      naturality := fun _ _ f => (S.map f).comm₁₂ }
  have h₁ : IsLimit
      ((ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤
        MetrizableLCA.{0}).mapCone cs) :=
    isLimitOfPreserves
      (ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}) hcs
  have h₂ : IsLimit
      ((ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤
        MetrizableLCA.{0}).mapCone cs) :=
    isLimitOfPreserves
      (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}) hcs
  rcases hlimit
    (S ⋙ (ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}))
    (S ⋙ (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}))
    α
    ((ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}).mapCone cs)
    ((ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}).mapCone cs)
    cs.pt.f
    h₁ h₂ hclosed
    (fun j => by simpa using (cs.π.app j).comm₁₂.symm) with
      ⟨hinj, hind, hclosedImage⟩
  exact closedEmbedding_of_injective_inducing_closedImage
    (cs.pt.f : cs.pt.X₁ → cs.pt.X₂) hinj hind hclosedImage

/-- WPP limits preserve the right open-map field of strict short complexes. -/
abbrev wppLimit_preserves_rightOpenMap : Prop :=
  ∀ (S : WalkingParallelPair ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cone S),
      IsLimit ((ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤
        MetrizableLCA.{0}).mapCone cs) →
        IsLimit ((ShortComplex.π₃ : ShortComplex MetrizableLCA.{0} ⥤
          MetrizableLCA.{0}).mapCone cs) →
          (∀ j : WalkingParallelPair,
            IsOpenMap ((S.obj j).g : (S.obj j).X₂ → (S.obj j).X₃)) →
            IsOpenMap (cs.pt.g : cs.pt.X₂ → cs.pt.X₃)

/-- Pure component-level LCA certificate for the right open-map WPP limit field. -/
abbrev wppLimit_lca_limitMap_preserves_openMap : Prop :=
  ∀ (X Y : WalkingParallelPair ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cone X) (cy : Cone Y) (φ : cx.pt ⟶ cy.pt),
      IsLimit cx →
        IsLimit cy →
          (∀ j : WalkingParallelPair, IsOpenMap (α.app j : X.obj j → Y.obj j)) →
            (∀ j : WalkingParallelPair, φ ≫ cy.π.app j = cx.π.app j ≫ α.app j) →
              IsOpenMap (φ : cx.pt → cy.pt)

/-- The pure LCA open-map certificate supplies the WPP limit right-open field. -/
theorem wppLimit_preserves_rightOpenMap_of_lca_limitMap
    (hlimit : wppLimit_lca_limitMap_preserves_openMap) :
    wppLimit_preserves_rightOpenMap := by
  intro S cs h₂ h₃ hopen
  let α : S ⋙ (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤
      MetrizableLCA.{0}) ⟶
      S ⋙ (ShortComplex.π₃ : ShortComplex MetrizableLCA.{0} ⥤
        MetrizableLCA.{0}) :=
    { app := fun j => (S.obj j).g
      naturality := fun _ _ f => (S.map f).comm₂₃ }
  exact hlimit
    (S ⋙ (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}))
    (S ⋙ (ShortComplex.π₃ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}))
    α
    ((ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}).mapCone cs)
    ((ShortComplex.π₃ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}).mapCone cs)
    cs.pt.g
    h₂ h₃ hopen
    (fun j => by simpa using (cs.π.app j).comm₂₃.symm)

/-- Quotient/equalizer-cover data for the pure component open-map input. -/
structure WppLimitLcaQuotientOpenMapData
    (X Y : WalkingParallelPair ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cone X) (cy : Cone Y) (φ : cx.pt ⟶ cy.pt) : Type 2 where
  QX : MetrizableLCA.{0}
  QY : MetrizableLCA.{0}
  qX : QX ⟶ cx.pt
  qY : QY ⟶ cy.pt
  G : QX ⟶ QY
  qX_surjective : Function.Surjective (qX : QX → cx.pt)
  qY_open : IsOpenMap (qY : QY → cy.pt)
  aggregate_open : IsOpenMap (G : QX → QY)
  quotient_comm : qX ≫ φ = G ≫ qY

/-- Closed-subgroup quotient-cover data supplying the quotient open-map package. -/
structure WppLimitLcaClosedQuotientCoverData
    (X Y : WalkingParallelPair ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cone X) (cy : Cone Y) (φ : cx.pt ⟶ cy.pt) : Type 2 where
  AX : MetrizableLCA.{0}
  AY : MetrizableLCA.{0}
  NX : AddSubgroup AX
  NY : AddSubgroup AY
  NX_closed : IsClosed (NX : Set AX)
  NY_closed : IsClosed (NY : Set AY)
  qX : MetrizableLCA.quotientObj AX NX NX_closed ⟶ cx.pt
  qY : MetrizableLCA.quotientObj AY NY NY_closed ⟶ cy.pt
  aggregate :
    MetrizableLCA.quotientObj AX NX NX_closed ⟶
      MetrizableLCA.quotientObj AY NY NY_closed
  qX_surjective : Function.Surjective
    (qX : MetrizableLCA.quotientObj AX NX NX_closed → cx.pt)
  qY_open : IsOpenMap
    (qY : MetrizableLCA.quotientObj AY NY NY_closed → cy.pt)
  aggregate_open : IsOpenMap
    (aggregate :
      MetrizableLCA.quotientObj AX NX NX_closed →
        MetrizableLCA.quotientObj AY NY NY_closed)
  quotient_comm : qX ≫ φ = aggregate ≫ qY

namespace WppLimitLcaClosedQuotientCoverData

variable {X Y : WalkingParallelPair ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
variable {cx : Cone X} {cy : Cone Y} {φ : cx.pt ⟶ cy.pt}

/-- The canonical source quotient map attached to closed quotient-cover data. -/
def sourceQuotientMap
    (d : WppLimitLcaClosedQuotientCoverData X Y α cx cy φ) :
    d.AX ⟶ MetrizableLCA.quotientObj d.AX d.NX d.NX_closed :=
  MetrizableLCA.quotientMap d.AX d.NX d.NX_closed

/-- The canonical target quotient map attached to closed quotient-cover data. -/
def targetQuotientMap
    (d : WppLimitLcaClosedQuotientCoverData X Y α cx cy φ) :
    d.AY ⟶ MetrizableLCA.quotientObj d.AY d.NY d.NY_closed :=
  MetrizableLCA.quotientMap d.AY d.NY d.NY_closed

theorem sourceQuotientMap_surjective
    (d : WppLimitLcaClosedQuotientCoverData X Y α cx cy φ) :
    Function.Surjective
      (d.sourceQuotientMap :
        d.AX → MetrizableLCA.quotientObj d.AX d.NX d.NX_closed) :=
  MetrizableLCA.quotientMap_surjective d.AX d.NX d.NX_closed

theorem sourceQuotientMap_open
    (d : WppLimitLcaClosedQuotientCoverData X Y α cx cy φ) :
    IsOpenMap
      (d.sourceQuotientMap :
        d.AX → MetrizableLCA.quotientObj d.AX d.NX d.NX_closed) :=
  MetrizableLCA.quotientMap_openMap d.AX d.NX d.NX_closed

theorem targetQuotientMap_surjective
    (d : WppLimitLcaClosedQuotientCoverData X Y α cx cy φ) :
    Function.Surjective
      (d.targetQuotientMap :
        d.AY → MetrizableLCA.quotientObj d.AY d.NY d.NY_closed) :=
  MetrizableLCA.quotientMap_surjective d.AY d.NY d.NY_closed

theorem targetQuotientMap_open
    (d : WppLimitLcaClosedQuotientCoverData X Y α cx cy φ) :
    IsOpenMap
      (d.targetQuotientMap :
        d.AY → MetrizableLCA.quotientObj d.AY d.NY d.NY_closed) :=
  MetrizableLCA.quotientMap_openMap d.AY d.NY d.NY_closed

/-- Closed quotient-cover data constructs quotient open-map data. -/
def toQuotientOpenMapData
    (d : WppLimitLcaClosedQuotientCoverData X Y α cx cy φ) :
    WppLimitLcaQuotientOpenMapData X Y α cx cy φ where
  QX := MetrizableLCA.quotientObj d.AX d.NX d.NX_closed
  QY := MetrizableLCA.quotientObj d.AY d.NY d.NY_closed
  qX := d.qX
  qY := d.qY
  G := d.aggregate
  qX_surjective := d.qX_surjective
  qY_open := d.qY_open
  aggregate_open := d.aggregate_open
  quotient_comm := d.quotient_comm

end WppLimitLcaClosedQuotientCoverData

/-- Quotient/equalizer-cover open-map data proves the pure component open-map input. -/
theorem wppLimit_lca_limitMap_preserves_openMap_of_quotientBoundary
    (hboundary :
      ∀ (X Y : WalkingParallelPair ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
        (cx : Cone X) (cy : Cone Y) (φ : cx.pt ⟶ cy.pt),
          IsLimit cx →
            IsLimit cy →
              (∀ j : WalkingParallelPair, IsOpenMap (α.app j : X.obj j → Y.obj j)) →
                (∀ j : WalkingParallelPair,
                  φ ≫ cy.π.app j = cx.π.app j ≫ α.app j) →
                  Nonempty (WppLimitLcaQuotientOpenMapData X Y α cx cy φ)) :
    wppLimit_lca_limitMap_preserves_openMap := by
  intro X Y α cx cy φ hcx hcy hopen hcompat
  rcases hboundary X Y α cx cy φ hcx hcy hopen hcompat with ⟨hdata⟩
  have hcomp : IsOpenMap ((hdata.qX ≫ φ : hdata.QX ⟶ cy.pt) :
      hdata.QX → cy.pt) := by
    rw [hdata.quotient_comm]
    exact hdata.qY_open.comp hdata.aggregate_open
  exact MetrizableLCA.isOpenMap_of_comp_surjective hdata.qX φ
    hdata.qX_surjective hcomp

/-- Closed quotient-cover data proves the pure component open-map input. -/
theorem wppLimit_lca_limitMap_preserves_openMap_of_closedQuotientCoverBoundary
    (hboundary :
      ∀ (X Y : WalkingParallelPair ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
        (cx : Cone X) (cy : Cone Y) (φ : cx.pt ⟶ cy.pt),
          IsLimit cx →
            IsLimit cy →
              (∀ j : WalkingParallelPair, IsOpenMap (α.app j : X.obj j → Y.obj j)) →
                (∀ j : WalkingParallelPair,
                  φ ≫ cy.π.app j = cx.π.app j ≫ α.app j) →
                  Nonempty (WppLimitLcaClosedQuotientCoverData X Y α cx cy φ)) :
    wppLimit_lca_limitMap_preserves_openMap :=
  wppLimit_lca_limitMap_preserves_openMap_of_quotientBoundary
    (fun X Y α cx cy φ hcx hcy hopen hcompat => by
      rcases hboundary X Y α cx cy φ hcx hcy hopen hcompat with ⟨d⟩
      exact ⟨d.toQuotientOpenMapData⟩)

/-- WPP limits preserve right surjectivity for strict short complexes. -/
abbrev rightSurjective_walkingParallelPair_limitClosure : Prop :=
  ∀ (S : WalkingParallelPair ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cone S),
      IsLimit cs →
        (∀ j : WalkingParallelPair, MetrizableLCA.strictShortExact (S.obj j)) →
          Function.Surjective (cs.pt.g : cs.pt.X₂ → cs.pt.X₃)

/-- Pure component-level LCA certificate for the right-surjectivity WPP limit field. -/
abbrev wppLimit_lca_limitMap_preserves_surjective : Prop :=
  ∀ (X Y : WalkingParallelPair ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cone X) (cy : Cone Y) (φ : cx.pt ⟶ cy.pt),
      IsLimit cx →
        IsLimit cy →
          (∀ j : WalkingParallelPair,
            Function.Surjective (α.app j : X.obj j → Y.obj j)) →
            (∀ j : WalkingParallelPair, φ ≫ cy.π.app j = cx.π.app j ≫ α.app j) →
              Function.Surjective (φ : cx.pt → cy.pt)

/-- Cokernel-top and open-map data for the induced WPP limit map. -/
abbrev WppLimitLcaRightSurjectiveCokernelTopBoundary : Prop :=
  ∀ (X Y : WalkingParallelPair ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cone X) (cy : Cone Y) (φ : cx.pt ⟶ cy.pt),
      IsLimit cx →
        IsLimit cy →
          (∀ j : WalkingParallelPair,
            Function.Surjective (α.app j : X.obj j → Y.obj j)) →
            (∀ j : WalkingParallelPair, φ ≫ cy.π.app j = cx.π.app j ≫ α.app j) →
              IsOpenMap (φ : cx.pt → cy.pt) ∧ MetrizableLCA.cokernelSubgroup φ = ⊤

/-- Cokernel-pi-zero and open-map data for the induced WPP limit map. -/
abbrev WppLimitLcaRightSurjectiveCokernelPiZeroBoundary : Prop :=
  ∀ (X Y : WalkingParallelPair ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cone X) (cy : Cone Y) (φ : cx.pt ⟶ cy.pt),
      IsLimit cx →
        IsLimit cy →
          (∀ j : WalkingParallelPair,
            Function.Surjective (α.app j : X.obj j → Y.obj j)) →
            (∀ j : WalkingParallelPair, φ ≫ cy.π.app j = cx.π.app j ≫ α.app j) →
              IsOpenMap (φ : cx.pt → cy.pt) ∧ MetrizableLCA.cokernelπ φ = 0

/-- Epi and open-map data for the induced WPP limit map. -/
abbrev WppLimitLcaRightSurjectiveEpiBoundary : Prop :=
  ∀ (X Y : WalkingParallelPair ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cone X) (cy : Cone Y) (φ : cx.pt ⟶ cy.pt),
      IsLimit cx →
        IsLimit cy →
          (∀ j : WalkingParallelPair,
            Function.Surjective (α.app j : X.obj j → Y.obj j)) →
            (∀ j : WalkingParallelPair, φ ≫ cy.π.app j = cx.π.app j ≫ α.app j) →
              IsOpenMap (φ : cx.pt → cy.pt) ∧ Epi φ

/-- The cokernel-top boundary supplies the pure WPP limit right-surjectivity input. -/
theorem wppLimit_lca_limitMap_preserves_surjective_of_cokernelTopBoundary
    (hboundary : WppLimitLcaRightSurjectiveCokernelTopBoundary) :
    wppLimit_lca_limitMap_preserves_surjective := by
  intro X Y α cx cy φ hcx hcy hsurj hcompat
  rcases hboundary X Y α cx cy φ hcx hcy hsurj hcompat with ⟨hopen, hcok⟩
  exact MetrizableLCA.surjective_of_cokernelSubgroup_eq_top_of_isOpenMap φ hcok hopen

/-- Cokernel-pi-zero data supplies the pure WPP limit right-surjectivity input. -/
theorem wppLimit_lca_limitMap_preserves_surjective_of_cokernelPiZeroBoundary
    (hboundary : WppLimitLcaRightSurjectiveCokernelPiZeroBoundary) :
    wppLimit_lca_limitMap_preserves_surjective :=
  wppLimit_lca_limitMap_preserves_surjective_of_cokernelTopBoundary
    (fun X Y α cx cy φ hcx hcy hsurj hcompat => by
      rcases hboundary X Y α cx cy φ hcx hcy hsurj hcompat with ⟨hopen, hπ⟩
      exact ⟨hopen, MetrizableLCA.cokernelSubgroup_eq_top_of_cokernelπ_eq_zero φ hπ⟩)

/-- Epi data supplies the pure WPP limit right-surjectivity input. -/
theorem wppLimit_lca_limitMap_preserves_surjective_of_epiBoundary
    (hboundary : WppLimitLcaRightSurjectiveEpiBoundary) :
    wppLimit_lca_limitMap_preserves_surjective :=
  wppLimit_lca_limitMap_preserves_surjective_of_cokernelPiZeroBoundary
    (fun X Y α cx cy φ hcx hcy hsurj hcompat => by
      rcases hboundary X Y α cx cy φ hcx hcy hsurj hcompat with ⟨hopen, hepi⟩
      haveI : Epi φ := hepi
      exact ⟨hopen, MetrizableLCA.cokernelπ_eq_zero_of_epi φ⟩)

/-- The pure LCA surjectivity certificate supplies the WPP limit right-surjective field. -/
theorem rightSurjective_walkingParallelPair_limitClosure_of_lca_limitMap
    (hlimit : wppLimit_lca_limitMap_preserves_surjective) :
    rightSurjective_walkingParallelPair_limitClosure := by
  intro S cs hcs hS
  let α : S ⋙ (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤
      MetrizableLCA.{0}) ⟶
      S ⋙ (ShortComplex.π₃ : ShortComplex MetrizableLCA.{0} ⥤
        MetrizableLCA.{0}) :=
    { app := fun j => (S.obj j).g
      naturality := fun _ _ f => (S.map f).comm₂₃ }
  have h₂ : IsLimit
      ((ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤
        MetrizableLCA.{0}).mapCone cs) :=
    isLimitOfPreserves
      (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}) hcs
  have h₃ : IsLimit
      ((ShortComplex.π₃ : ShortComplex MetrizableLCA.{0} ⥤
        MetrizableLCA.{0}).mapCone cs) :=
    isLimitOfPreserves
      (ShortComplex.π₃ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}) hcs
  exact hlimit
    (S ⋙ (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}))
    (S ⋙ (ShortComplex.π₃ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}))
    α
    ((ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}).mapCone cs)
    ((ShortComplex.π₃ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}).mapCone cs)
    cs.pt.g
    h₂ h₃ (fun j => (hS j).surjective)
    (fun j => by simpa using (cs.π.app j).comm₂₃.symm)

/--
Concrete correction data for the WPP limit right-surjectivity field.  A target
limit element is lifted at the zero component and then corrected by a source
degree-one boundary so that the corrected zero-component lift equalizes the two
parallel arrows.
-/
abbrev rightSurjective_walkingParallelPair_limitZeroCorrectionBoundary : Prop :=
  ∀ (S : WalkingParallelPair ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cone S),
      IsLimit cs →
        (∀ j : WalkingParallelPair, MetrizableLCA.strictShortExact (S.obj j)) →
          ∀ y₃ : cs.pt.X₃,
            ∃ (x₂₀ : (S.obj WalkingParallelPair.zero).X₂)
              (u₁₀ : (S.obj WalkingParallelPair.zero).X₁),
                (S.obj WalkingParallelPair.zero).g x₂₀ =
                  (cs.π.app WalkingParallelPair.zero).τ₃ y₃ ∧
                  (S.map WalkingParallelPairHom.left).τ₂
                      (x₂₀ - (S.obj WalkingParallelPair.zero).f u₁₀) =
                  (S.map WalkingParallelPairHom.right).τ₂
                      (x₂₀ - (S.obj WalkingParallelPair.zero).f u₁₀)

/--
Difference-form correction data for the WPP limit right-surjectivity field.  The
chosen zero-component lift is corrected when its left/right difference is the
image of a source-degree-one difference.
-/
abbrev rightSurjective_walkingParallelPair_limitDifferenceCorrectionBoundary : Prop :=
  ∀ (S : WalkingParallelPair ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cone S),
      IsLimit cs →
        (∀ j : WalkingParallelPair, MetrizableLCA.strictShortExact (S.obj j)) →
          ∀ y₃ : cs.pt.X₃,
            ∃ (x₂₀ : (S.obj WalkingParallelPair.zero).X₂)
              (u₁₀ : (S.obj WalkingParallelPair.zero).X₁),
                (S.obj WalkingParallelPair.zero).g x₂₀ =
                  (cs.π.app WalkingParallelPair.zero).τ₃ y₃ ∧
                  (S.map WalkingParallelPairHom.left).τ₂ x₂₀ -
                      (S.map WalkingParallelPairHom.right).τ₂ x₂₀ =
                    (S.obj WalkingParallelPair.one).f
                      ((S.map WalkingParallelPairHom.left).τ₁ u₁₀ -
                        (S.map WalkingParallelPairHom.right).τ₁ u₁₀)

/--
Source-difference data for the WPP limit right-surjectivity field.  It asks
that every degree-one element at object one be a left/right difference of a
degree-one element at object zero.
-/
abbrev rightSurjective_walkingParallelPair_limitSourceDifferenceSurjectiveBoundary :
    Prop :=
  ∀ (S : WalkingParallelPair ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cone S),
      IsLimit cs →
        (∀ j : WalkingParallelPair, MetrizableLCA.strictShortExact (S.obj j)) →
          Function.Surjective
            (fun u₁₀ : (S.obj WalkingParallelPair.zero).X₁ =>
              (S.map WalkingParallelPairHom.left).τ₁ u₁₀ -
                (S.map WalkingParallelPairHom.right).τ₁ u₁₀)

/--
Surjectivity of the source degree-one left/right difference map supplies the
difference-form correction boundary.
-/
theorem
    rightSurjective_walkingParallelPair_limitDifferenceCorrectionBoundary_of_sourceDifferenceSurjectiveBoundary
    (hboundary :
      rightSurjective_walkingParallelPair_limitSourceDifferenceSurjectiveBoundary) :
    rightSurjective_walkingParallelPair_limitDifferenceCorrectionBoundary := by
  intro S cs hcs hS y₃
  rcases (hS WalkingParallelPair.zero).surjective
      ((cs.π.app WalkingParallelPair.zero).τ₃ y₃) with
    ⟨x₂₀, hx₂₀⟩
  let d₂ : (S.obj WalkingParallelPair.one).X₂ :=
    (S.map WalkingParallelPairHom.left).τ₂ x₂₀ -
      (S.map WalkingParallelPairHom.right).τ₂ x₂₀
  have hleft_g :
      (S.obj WalkingParallelPair.one).g
          ((S.map WalkingParallelPairHom.left).τ₂ x₂₀) =
        (S.map WalkingParallelPairHom.left).τ₃
          ((S.obj WalkingParallelPair.zero).g x₂₀) := by
    exact congrArg
      (fun h : (S.obj WalkingParallelPair.zero).X₂ ⟶
          (S.obj WalkingParallelPair.one).X₃ => h x₂₀)
      (S.map WalkingParallelPairHom.left).comm₂₃
  have hright_g :
      (S.obj WalkingParallelPair.one).g
          ((S.map WalkingParallelPairHom.right).τ₂ x₂₀) =
        (S.map WalkingParallelPairHom.right).τ₃
          ((S.obj WalkingParallelPair.zero).g x₂₀) := by
    exact congrArg
      (fun h : (S.obj WalkingParallelPair.zero).X₂ ⟶
          (S.obj WalkingParallelPair.one).X₃ => h x₂₀)
      (S.map WalkingParallelPairHom.right).comm₂₃
  have hleftπ :
      (S.map WalkingParallelPairHom.left).τ₃
          ((cs.π.app WalkingParallelPair.zero).τ₃ y₃) =
        (cs.π.app WalkingParallelPair.one).τ₃ y₃ := by
    change ((cs.π.app WalkingParallelPair.zero ≫
      S.map WalkingParallelPairHom.left).τ₃) y₃ =
        (cs.π.app WalkingParallelPair.one).τ₃ y₃
    exact congrArg
      (fun h : cs.pt ⟶ S.obj WalkingParallelPair.one => h.τ₃ y₃)
      (cs.w WalkingParallelPairHom.left)
  have hrightπ :
      (S.map WalkingParallelPairHom.right).τ₃
          ((cs.π.app WalkingParallelPair.zero).τ₃ y₃) =
        (cs.π.app WalkingParallelPair.one).τ₃ y₃ := by
    change ((cs.π.app WalkingParallelPair.zero ≫
      S.map WalkingParallelPairHom.right).τ₃) y₃ =
        (cs.π.app WalkingParallelPair.one).τ₃ y₃
    exact congrArg
      (fun h : cs.pt ⟶ S.obj WalkingParallelPair.one => h.τ₃ y₃)
      (cs.w WalkingParallelPairHom.right)
  have hd₂_zero : (S.obj WalkingParallelPair.one).g d₂ = 0 := by
    calc
      (S.obj WalkingParallelPair.one).g d₂ =
          (S.obj WalkingParallelPair.one).g
              ((S.map WalkingParallelPairHom.left).τ₂ x₂₀) -
            (S.obj WalkingParallelPair.one).g
              ((S.map WalkingParallelPairHom.right).τ₂ x₂₀) := by
          simp [d₂, map_sub]
      _ = (S.map WalkingParallelPairHom.left).τ₃
            ((S.obj WalkingParallelPair.zero).g x₂₀) -
          (S.map WalkingParallelPairHom.right).τ₃
            ((S.obj WalkingParallelPair.zero).g x₂₀) := by
          rw [hleft_g, hright_g]
      _ = (S.map WalkingParallelPairHom.left).τ₃
            ((cs.π.app WalkingParallelPair.zero).τ₃ y₃) -
          (S.map WalkingParallelPairHom.right).τ₃
            ((cs.π.app WalkingParallelPair.zero).τ₃ y₃) := by
          rw [hx₂₀]
      _ = (cs.π.app WalkingParallelPair.one).τ₃ y₃ -
          (cs.π.app WalkingParallelPair.one).τ₃ y₃ := by
          rw [hleftπ, hrightπ]
      _ = 0 := sub_self _
  rcases (hS WalkingParallelPair.one).algebraic_exact d₂ hd₂_zero with
    ⟨v₁, hv₁⟩
  rcases hboundary S cs hcs hS v₁ with ⟨u₁₀, hu₁₀⟩
  refine ⟨x₂₀, u₁₀, hx₂₀, ?_⟩
  calc
    (S.map WalkingParallelPairHom.left).τ₂ x₂₀ -
        (S.map WalkingParallelPairHom.right).τ₂ x₂₀ = d₂ := rfl
    _ = (S.obj WalkingParallelPair.one).f v₁ := hv₁.symm
    _ = (S.obj WalkingParallelPair.one).f
        ((S.map WalkingParallelPairHom.left).τ₁ u₁₀ -
          (S.map WalkingParallelPairHom.right).τ₁ u₁₀) := by
        rw [← hu₁₀]

/--
The difference-form correction boundary supplies the concrete zero-component
correction boundary used by the WPP limit equalizer argument.
-/
theorem rightSurjective_walkingParallelPair_limitZeroCorrectionBoundary_of_differenceCorrectionBoundary
    (hboundary : rightSurjective_walkingParallelPair_limitDifferenceCorrectionBoundary) :
    rightSurjective_walkingParallelPair_limitZeroCorrectionBoundary := by
  intro S cs hcs hS y₃
  rcases hboundary S cs hcs hS y₃ with ⟨x₂₀, u₁₀, hx₂₀, hdiff⟩
  refine ⟨x₂₀, u₁₀, hx₂₀, ?_⟩
  have hleft_f :
      (S.map WalkingParallelPairHom.left).τ₂
          ((S.obj WalkingParallelPair.zero).f u₁₀) =
        (S.obj WalkingParallelPair.one).f
          ((S.map WalkingParallelPairHom.left).τ₁ u₁₀) := by
    exact (congrArg
      (fun h : (S.obj WalkingParallelPair.zero).X₁ ⟶
          (S.obj WalkingParallelPair.one).X₂ => h u₁₀)
      (S.map WalkingParallelPairHom.left).comm₁₂).symm
  have hright_f :
      (S.map WalkingParallelPairHom.right).τ₂
          ((S.obj WalkingParallelPair.zero).f u₁₀) =
        (S.obj WalkingParallelPair.one).f
          ((S.map WalkingParallelPairHom.right).τ₁ u₁₀) := by
    exact (congrArg
      (fun h : (S.obj WalkingParallelPair.zero).X₁ ⟶
          (S.obj WalkingParallelPair.one).X₂ => h u₁₀)
      (S.map WalkingParallelPairHom.right).comm₁₂).symm
  have hdiff' :
      (S.map WalkingParallelPairHom.left).τ₂ x₂₀ -
          (S.map WalkingParallelPairHom.right).τ₂ x₂₀ =
        (S.obj WalkingParallelPair.one).f
            ((S.map WalkingParallelPairHom.left).τ₁ u₁₀) -
          (S.obj WalkingParallelPair.one).f
            ((S.map WalkingParallelPairHom.right).τ₁ u₁₀) := by
    simpa [map_sub] using hdiff
  rw [map_sub, map_sub, hleft_f, hright_f]
  exact sub_eq_sub_iff_sub_eq_sub.mpr hdiff'

/--
The zero-component correction boundary supplies the WPP limit
right-surjectivity field.  This uses the equalizer model of a WPP limit to turn
the corrected zero-component lift into an actual element of the limit.
-/
theorem rightSurjective_walkingParallelPair_limitClosure_of_zeroCorrectionBoundary
    (hboundary : rightSurjective_walkingParallelPair_limitZeroCorrectionBoundary) :
    rightSurjective_walkingParallelPair_limitClosure := by
  intro S cs hcs hS y₃
  rcases hboundary S cs hcs hS y₃ with ⟨x₂₀, u₁₀, hx₂₀, hcorr⟩
  let c₂ : Cone (S ⋙ (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤
      MetrizableLCA.{0})) :=
    (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}).mapCone cs
  let c₃ : Cone (S ⋙ (ShortComplex.π₃ : ShortComplex MetrizableLCA.{0} ⥤
      MetrizableLCA.{0})) :=
    (ShortComplex.π₃ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}).mapCone cs
  have hc₂ : IsLimit c₂ := by
    simpa [c₂] using
      (isLimitOfPreserves
        (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}) hcs)
  have hc₃ : IsLimit c₃ := by
    simpa [c₃] using
      (isLimitOfPreserves
        (ShortComplex.π₃ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}) hcs)
  let z : MetrizableLCA.equalizerObj
      (S.map WalkingParallelPairHom.left).τ₂
      (S.map WalkingParallelPairHom.right).τ₂ :=
    ⟨x₂₀ - (S.obj WalkingParallelPair.zero).f u₁₀, hcorr⟩
  let f₂ : Fork (S.map WalkingParallelPairHom.left).τ₂
      (S.map WalkingParallelPairHom.right).τ₂ :=
    Fork.ofCone c₂
  have hf₂ : IsLimit f₂ := by
    simpa [f₂, c₂] using forkOfConeIsLimit hc₂
  let e₂ := IsLimit.conePointUniqueUpToIso hf₂
    (MetrizableLCA.equalizerIsLimit
      (S.map WalkingParallelPairHom.left).τ₂
      (S.map WalkingParallelPairHom.right).τ₂)
  let x₂ : cs.pt.X₂ := e₂.inv z
  refine ⟨x₂, ?_⟩
  have he₂_inv :
      e₂.inv ≫ (Fork.ofCone c₂).ι =
        MetrizableLCA.equalizerι
          (S.map WalkingParallelPairHom.left).τ₂
          (S.map WalkingParallelPairHom.right).τ₂ := by
    simpa [e₂] using
      (IsLimit.conePointUniqueUpToIso_inv_comp hf₂
        (MetrizableLCA.equalizerIsLimit
          (S.map WalkingParallelPairHom.left).τ₂
          (S.map WalkingParallelPairHom.right).τ₂)
        WalkingParallelPair.zero)
  have hx₂π :
      (cs.π.app WalkingParallelPair.zero).τ₂ x₂ =
        x₂₀ - (S.obj WalkingParallelPair.zero).f u₁₀ := by
    change (e₂.inv ≫ (Fork.ofCone c₂).ι) z =
      x₂₀ - (S.obj WalkingParallelPair.zero).f u₁₀
    rw [he₂_inv]
    rfl
  have hπ₃₀ : IsClosedEmbedding
      ((cs.π.app WalkingParallelPair.zero).τ₃ :
        cs.pt.X₃ → (S.obj WalkingParallelPair.zero).X₃) := by
    simpa [c₃] using
      walkingParallelPair_limit_π_zero_closedEmbedding (F :=
        S ⋙ (ShortComplex.π₃ : ShortComplex MetrizableLCA.{0} ⥤
          MetrizableLCA.{0})) hc₃
  apply hπ₃₀.injective
  calc
    (cs.π.app WalkingParallelPair.zero).τ₃ (cs.pt.g x₂) =
        (S.obj WalkingParallelPair.zero).g
          ((cs.π.app WalkingParallelPair.zero).τ₂ x₂) := by
        exact congrArg
          (fun h : cs.pt.X₂ ⟶ (S.obj WalkingParallelPair.zero).X₃ => h x₂)
          (cs.π.app WalkingParallelPair.zero).comm₂₃.symm
    _ = (S.obj WalkingParallelPair.zero).g
        (x₂₀ - (S.obj WalkingParallelPair.zero).f u₁₀) := by
        rw [hx₂π]
    _ = (S.obj WalkingParallelPair.zero).g x₂₀ := by
        have hzero :
            (S.obj WalkingParallelPair.zero).g
              ((S.obj WalkingParallelPair.zero).f u₁₀) = 0 := by
          exact congrArg
            (fun h : (S.obj WalkingParallelPair.zero).X₁ ⟶
                (S.obj WalkingParallelPair.zero).X₃ => h u₁₀)
            (S.obj WalkingParallelPair.zero).zero
        simp [map_sub, hzero]
    _ = (cs.π.app WalkingParallelPair.zero).τ₃ y₃ := hx₂₀

/--
The difference-form correction boundary supplies the WPP limit
right-surjectivity field via the zero-component correction argument.
-/
theorem rightSurjective_walkingParallelPair_limitClosure_of_differenceCorrectionBoundary
    (hboundary : rightSurjective_walkingParallelPair_limitDifferenceCorrectionBoundary) :
    rightSurjective_walkingParallelPair_limitClosure :=
  rightSurjective_walkingParallelPair_limitClosure_of_zeroCorrectionBoundary
    (rightSurjective_walkingParallelPair_limitZeroCorrectionBoundary_of_differenceCorrectionBoundary
      hboundary)

/--
Source-difference surjectivity supplies the WPP limit right-surjectivity field.
-/
theorem rightSurjective_walkingParallelPair_limitClosure_of_sourceDifferenceSurjectiveBoundary
    (hboundary :
      rightSurjective_walkingParallelPair_limitSourceDifferenceSurjectiveBoundary) :
    rightSurjective_walkingParallelPair_limitClosure :=
  rightSurjective_walkingParallelPair_limitClosure_of_differenceCorrectionBoundary
    (rightSurjective_walkingParallelPair_limitDifferenceCorrectionBoundary_of_sourceDifferenceSurjectiveBoundary
        hboundary)

/-- Direct algebraic exactness at the WPP limit point. -/
abbrev algebraicExact_walkingParallelPair_limitClosure : Prop :=
  ∀ (S : WalkingParallelPair ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cone S),
      IsLimit cs →
        (∀ j : WalkingParallelPair, MetrizableLCA.strictShortExact (S.obj j)) →
          ∀ x₂ : cs.pt.X₂, cs.pt.g x₂ = 0 → ∃ x₁ : cs.pt.X₁, cs.pt.f x₁ = x₂

/-- Component-level algebraic exactness certificate for WPP short-complex limits. -/
abbrev wppLimit_lca_limitShortComplex_algebraicExact : Prop :=
  ∀ (S : WalkingParallelPair ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cone S),
      IsLimit ((ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤
        MetrizableLCA.{0}).mapCone cs) →
        IsLimit ((ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤
          MetrizableLCA.{0}).mapCone cs) →
          IsLimit ((ShortComplex.π₃ : ShortComplex MetrizableLCA.{0} ⥤
            MetrizableLCA.{0}).mapCone cs) →
            (∀ j : WalkingParallelPair,
              ∀ x₂ : (S.obj j).X₂, (S.obj j).g x₂ = 0 →
                ∃ x₁ : (S.obj j).X₁, (S.obj j).f x₁ = x₂) →
              ∀ x₂ : cs.pt.X₂, cs.pt.g x₂ = 0 →
                ∃ x₁ : cs.pt.X₁, cs.pt.f x₁ = x₂

/-- The component certificate supplies algebraic exactness at WPP limits. -/
theorem algebraicExact_walkingParallelPair_limitClosure_of_lca_limitShortComplex
    (hlimit : wppLimit_lca_limitShortComplex_algebraicExact) :
    algebraicExact_walkingParallelPair_limitClosure := by
  intro S cs hcs hS
  exact hlimit S cs
    (isLimitOfPreserves
      (ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}) hcs)
    (isLimitOfPreserves
      (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}) hcs)
    (isLimitOfPreserves
      (ShortComplex.π₃ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}) hcs)
    (fun j => (hS j).algebraic_exact)

/--
Direct algebraic exactness at a WPP limit of strict short exact complexes.
The pointwise left closed-embedding hypotheses supply the injectivity needed to
make the componentwise algebraic lifts compatible with the two parallel arrows.
-/
theorem algebraicExact_walkingParallelPair_limitClosure_direct :
    algebraicExact_walkingParallelPair_limitClosure := by
  intro S cs hcs hS x₂ hx₂
  let c₁ : Cone (S ⋙ (ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤
      MetrizableLCA.{0})) :=
    (ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}).mapCone cs
  let c₂ : Cone (S ⋙ (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤
      MetrizableLCA.{0})) :=
    (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}).mapCone cs
  have hc₁ : IsLimit c₁ := by
    simpa [c₁] using
      (isLimitOfPreserves
        (ShortComplex.π₁ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}) hcs)
  have hc₂ : IsLimit c₂ := by
    simpa [c₂] using
      (isLimitOfPreserves
        (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}) hcs)
  let x₂₀ : (S.obj WalkingParallelPair.zero).X₂ :=
    (cs.π.app WalkingParallelPair.zero).τ₂ x₂
  have hx₂₀ : (S.obj WalkingParallelPair.zero).g x₂₀ = 0 := by
    calc
      (S.obj WalkingParallelPair.zero).g x₂₀ =
          (cs.π.app WalkingParallelPair.zero).τ₃ (cs.pt.g x₂) := by
          exact congrArg
            (fun h : cs.pt.X₂ ⟶ (S.obj WalkingParallelPair.zero).X₃ => h x₂)
            (cs.π.app WalkingParallelPair.zero).comm₂₃
      _ = 0 := by
        rw [hx₂]
        simp
  rcases (hS WalkingParallelPair.zero).algebraic_exact x₂₀ hx₂₀ with
    ⟨x₁₀, hx₁₀⟩
  have hx₁₀_equalizes :
      ((S.map WalkingParallelPairHom.left).τ₁) x₁₀ =
        ((S.map WalkingParallelPairHom.right).τ₁) x₁₀ := by
    apply (hS WalkingParallelPair.one).closed_inclusion.injective
    calc
      (S.obj WalkingParallelPair.one).f
          (((S.map WalkingParallelPairHom.left).τ₁) x₁₀) =
          (S.map WalkingParallelPairHom.left).τ₂
            ((S.obj WalkingParallelPair.zero).f x₁₀) := by
          exact congrArg
            (fun h : (S.obj WalkingParallelPair.zero).X₁ ⟶
                (S.obj WalkingParallelPair.one).X₂ => h x₁₀)
            (S.map WalkingParallelPairHom.left).comm₁₂
      _ = (S.map WalkingParallelPairHom.left).τ₂ x₂₀ := by
        rw [hx₁₀]
      _ = (cs.π.app WalkingParallelPair.one).τ₂ x₂ := by
        change ((cs.π.app WalkingParallelPair.zero ≫
          S.map WalkingParallelPairHom.left).τ₂) x₂ =
          (cs.π.app WalkingParallelPair.one).τ₂ x₂
        exact congrArg (fun h : cs.pt ⟶ S.obj WalkingParallelPair.one => h.τ₂ x₂)
          (cs.w WalkingParallelPairHom.left)
      _ = (S.map WalkingParallelPairHom.right).τ₂ x₂₀ := by
        change (cs.π.app WalkingParallelPair.one).τ₂ x₂ =
          ((cs.π.app WalkingParallelPair.zero ≫
            S.map WalkingParallelPairHom.right).τ₂) x₂
        exact (congrArg (fun h : cs.pt ⟶ S.obj WalkingParallelPair.one => h.τ₂ x₂)
          (cs.w WalkingParallelPairHom.right)).symm
      _ = (S.map WalkingParallelPairHom.right).τ₂
          ((S.obj WalkingParallelPair.zero).f x₁₀) := by
        rw [hx₁₀]
      _ = (S.obj WalkingParallelPair.one).f
          (((S.map WalkingParallelPairHom.right).τ₁) x₁₀) := by
          exact (congrArg
            (fun h : (S.obj WalkingParallelPair.zero).X₁ ⟶
                (S.obj WalkingParallelPair.one).X₂ => h x₁₀)
            (S.map WalkingParallelPairHom.right).comm₁₂).symm
  let z : MetrizableLCA.equalizerObj
      (S.map WalkingParallelPairHom.left).τ₁
      (S.map WalkingParallelPairHom.right).τ₁ :=
    ⟨x₁₀, hx₁₀_equalizes⟩
  let f₁ : Fork (S.map WalkingParallelPairHom.left).τ₁
      (S.map WalkingParallelPairHom.right).τ₁ :=
    Fork.ofCone c₁
  have hf₁ : IsLimit f₁ := by
    simpa [f₁, c₁] using forkOfConeIsLimit hc₁
  let e₁ := IsLimit.conePointUniqueUpToIso hf₁
    (MetrizableLCA.equalizerIsLimit
      (S.map WalkingParallelPairHom.left).τ₁
      (S.map WalkingParallelPairHom.right).τ₁)
  let x₁ : cs.pt.X₁ := e₁.inv z
  refine ⟨x₁, ?_⟩
  have he₁_inv :
      e₁.inv ≫ (Fork.ofCone c₁).ι =
        MetrizableLCA.equalizerι
          (S.map WalkingParallelPairHom.left).τ₁
          (S.map WalkingParallelPairHom.right).τ₁ := by
    simpa [e₁] using
      (IsLimit.conePointUniqueUpToIso_inv_comp hf₁
        (MetrizableLCA.equalizerIsLimit
          (S.map WalkingParallelPairHom.left).τ₁
          (S.map WalkingParallelPairHom.right).τ₁)
        WalkingParallelPair.zero)
  have hx₁π :
      (cs.π.app WalkingParallelPair.zero).τ₁ x₁ = x₁₀ := by
    change (e₁.inv ≫ (Fork.ofCone c₁).ι) z = x₁₀
    rw [he₁_inv]
    rfl
  have hπ₂₀ : IsClosedEmbedding
      ((cs.π.app WalkingParallelPair.zero).τ₂ :
        cs.pt.X₂ → (S.obj WalkingParallelPair.zero).X₂) := by
    simpa [c₂] using
      walkingParallelPair_limit_π_zero_closedEmbedding (F :=
        S ⋙ (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤
          MetrizableLCA.{0})) hc₂
  apply hπ₂₀.injective
  calc
    (cs.π.app WalkingParallelPair.zero).τ₂ (cs.pt.f x₁) =
        (S.obj WalkingParallelPair.zero).f
          ((cs.π.app WalkingParallelPair.zero).τ₁ x₁) := by
        exact (congrArg
          (fun h : cs.pt.X₁ ⟶ (S.obj WalkingParallelPair.zero).X₂ => h x₁)
          (cs.π.app WalkingParallelPair.zero).comm₁₂).symm
    _ = (S.obj WalkingParallelPair.zero).f x₁₀ := by
      rw [hx₁π]
    _ = x₂₀ := hx₁₀
    _ = (cs.π.app WalkingParallelPair.zero).τ₂ x₂ := rfl

/-- Left field consumer for the WPP limit-closure route. -/
theorem leftClosedEmbedding_walkingParallelPair_limitClosure_of_preserves
    (hpres : wppLimit_preserves_leftClosedEmbedding) :
    ∀ (S : WalkingParallelPair ⥤ ShortComplex MetrizableLCA.{0})
      (cs : Cone S),
        IsLimit cs →
          (∀ j : WalkingParallelPair, MetrizableLCA.strictShortExact (S.obj j)) →
            IsClosedEmbedding (cs.pt.f : cs.pt.X₁ → cs.pt.X₂) := by
  intro S cs hcs hS
  exact hpres S cs hcs (fun j => (hS j).closed_inclusion)

/-- Right-open field consumer for the WPP limit-closure route. -/
theorem rightOpenMap_walkingParallelPair_limitClosure_of_preserves
    (hpres : wppLimit_preserves_rightOpenMap) :
    ∀ (S : WalkingParallelPair ⥤ ShortComplex MetrizableLCA.{0})
      (cs : Cone S),
        IsLimit cs →
          (∀ j : WalkingParallelPair, MetrizableLCA.strictShortExact (S.obj j)) →
            IsOpenMap (cs.pt.g : cs.pt.X₂ → cs.pt.X₃) := by
  intro S cs hcs hS
  exact hpres S cs
    (isLimitOfPreserves
      (ShortComplex.π₂ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}) hcs)
    (isLimitOfPreserves
      (ShortComplex.π₃ : ShortComplex MetrizableLCA.{0} ⥤ MetrizableLCA.{0}) hcs)
    (fun j => (hS j).open_map)

/-- Strict exactness at WPP limits from the four short-complex field inputs. -/
theorem strictShortExact_walkingParallelPair_limitClosure_of_fields
    (hleft : wppLimit_preserves_leftClosedEmbedding)
    (hrightOpen : wppLimit_preserves_rightOpenMap)
    (hrightSurj : rightSurjective_walkingParallelPair_limitClosure)
    (halg : algebraicExact_walkingParallelPair_limitClosure) :
    ∀ (S : WalkingParallelPair ⥤ ShortComplex MetrizableLCA.{0})
      (cs : Cone S),
        IsLimit cs →
          (∀ j : WalkingParallelPair, MetrizableLCA.strictShortExact (S.obj j)) →
            MetrizableLCA.strictShortExact cs.pt := by
  intro S cs hcs hS
  exact
    { closed_inclusion :=
        leftClosedEmbedding_walkingParallelPair_limitClosure_of_preserves
          hleft S cs hcs hS
      open_map :=
        rightOpenMap_walkingParallelPair_limitClosure_of_preserves
          hrightOpen S cs hcs hS
      surjective := hrightSurj S cs hcs hS
      algebraic_exact := halg S cs hcs hS }

/-- WPP exact-acyclic limit closure from four short-complex field inputs. -/
theorem exactAcyclic_walkingParallelPair_limitClosure_of_fields
    (hleft : wppLimit_preserves_leftClosedEmbedding)
    (hrightOpen : wppLimit_preserves_rightOpenMap)
    (hrightSurj : rightSurjective_walkingParallelPair_limitClosure)
    (halg : algebraicExact_walkingParallelPair_limitClosure) :
    exactAcyclic_metrizableLCA_walkingParallelPair_limitClosure := by
  intro K ck hck hK i
  let S : WalkingParallelPair ⥤ ShortComplex MetrizableLCA.{0} :=
    K ⋙ degreeShortComplexFunctor i
  let cs : Cone S := (degreeShortComplexFunctor i).mapCone ck
  have hcs : IsLimit cs := by
    refine ShortComplex.isLimitOfIsLimitπ _ ?_ ?_ ?_
    · simpa [degreeShortComplexFunctor, HomologicalComplex.shortComplexFunctor, cs] using
        (isLimitOfPreserves
          (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ)
            ((ComplexShape.up ℤ).prev i)) hck)
    · simpa [degreeShortComplexFunctor, HomologicalComplex.shortComplexFunctor, cs] using
        (isLimitOfPreserves
          (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) i) hck)
    · simpa [degreeShortComplexFunctor, HomologicalComplex.shortComplexFunctor, cs] using
        (isLimitOfPreserves
          (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ)
            ((ComplexShape.up ℤ).next i)) hck)
  have hS : ∀ j : WalkingParallelPair, MetrizableLCA.strictShortExact (S.obj j) := by
    intro j
    exact hK j i
  exact strictShortExact_walkingParallelPair_limitClosure_of_fields
    hleft hrightOpen hrightSurj halg S cs hcs hS

/--
WPP exact-acyclic limit closure with the left closed-embedding and algebraic
exactness fields supplied directly. The remaining work is the right
open-map and right-surjectivity behavior of WPP limits.
-/
theorem exactAcyclic_walkingParallelPair_limitClosure_of_directLeftAlgebraic
    (hrightOpen : wppLimit_preserves_rightOpenMap)
    (hrightSurj : rightSurjective_walkingParallelPair_limitClosure) :
    exactAcyclic_metrizableLCA_walkingParallelPair_limitClosure :=
  exactAcyclic_walkingParallelPair_limitClosure_of_fields
    (wppLimit_preserves_leftClosedEmbedding_of_injective_inducing_closedImage
      wppLimit_lca_limitMap_injective_inducing_closedImage_direct)
    hrightOpen hrightSurj
    algebraicExact_walkingParallelPair_limitClosure_direct

/-- Comparison and closure prove exact acyclicity of a WPP limit comparison cone. -/
theorem exactAcyclic_mappingCone_of_walkingParallelPair_comparison_and_limitClosure
    (hcomparison : mappingCone_boundedInclusion_walkingParallelPair_limitComparison)
    (hclosure : exactAcyclic_metrizableLCA_walkingParallelPair_limitClosure)
    (X₁ X₂ : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0})
    (c₁ : Cone X₁) (c₂ : Cone X₂)
    (hc₁ : IsLimit c₁) (hc₂ : IsLimit c₂) (f : X₁ ⟶ X₂)
    (hf : directWeakEquivalence.functorCategory WalkingParallelPair f)
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j : WalkingParallelPair,
      φ ≫ c₂.π.app j = c₁.π.app j ≫ f.app j) :
    exactAcyclic MetrizableLCA
      (CochainComplex.mappingCone
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)) := by
  rcases hcomparison X₁ X₂ c₁ c₂ hc₁ hc₂ f hf φ hφ with
    ⟨K, ck, ⟨hck⟩, hK, ⟨e⟩⟩
  exact exactAcyclic_of_iso MetrizableLCA e.symm (hclosure K ck hck hK)

/-- The comparison and closure inputs supply the direct WPP limit constructor condition. -/
theorem directWalkingParallelPairLimitCondition_of_comparison_and_limitClosure
    (hcomparison : mappingCone_boundedInclusion_walkingParallelPair_limitComparison)
    (hclosure : exactAcyclic_metrizableLCA_walkingParallelPair_limitClosure) :
    DirectWalkingParallelPairLimitCondition := by
  intro X₁ X₂ c₁ c₂ hc₁ hc₂ f hf φ hφ
  exact
    exactAcyclic_mappingCone_of_walkingParallelPair_comparison_and_limitClosure
      hcomparison hclosure X₁ X₂ c₁ c₂ hc₁ hc₂ f hf φ hφ

/-- Direct WPP limit stability from comparison and exact-acyclic closure. -/
theorem directWalkingParallelPairLimitStability_of_comparison_and_limitClosure
    (hcomparison : mappingCone_boundedInclusion_walkingParallelPair_limitComparison)
    (hclosure : exactAcyclic_metrizableLCA_walkingParallelPair_limitClosure) :
    DirectWalkingParallelPairLimitStability :=
  MorphismProperty.IsStableUnderLimitsOfShape.mk
    (directWalkingParallelPairLimitCondition_of_comparison_and_limitClosure
      hcomparison hclosure)

/-- Direct WPP limit stability from comparison and short-complex limit field inputs. -/
theorem directWalkingParallelPairLimitStability_of_comparison_and_limitFields
    (hcomparison : mappingCone_boundedInclusion_walkingParallelPair_limitComparison)
    (hleft : wppLimit_preserves_leftClosedEmbedding)
    (hrightOpen : wppLimit_preserves_rightOpenMap)
    (hrightSurj : rightSurjective_walkingParallelPair_limitClosure)
    (halg : algebraicExact_walkingParallelPair_limitClosure) :
    DirectWalkingParallelPairLimitStability :=
  directWalkingParallelPairLimitStability_of_comparison_and_limitClosure
    hcomparison
    (exactAcyclic_walkingParallelPair_limitClosure_of_fields
      hleft hrightOpen hrightSurj halg)

/-- Direct WPP limit stability with direct left and algebraic fields. -/
theorem directWalkingParallelPairLimitStability_of_comparison_and_directLeftAlgebraic
    (hcomparison : mappingCone_boundedInclusion_walkingParallelPair_limitComparison)
    (hrightOpen : wppLimit_preserves_rightOpenMap)
    (hrightSurj : rightSurjective_walkingParallelPair_limitClosure) :
    DirectWalkingParallelPairLimitStability :=
  directWalkingParallelPairLimitStability_of_comparison_and_limitClosure
    hcomparison
    (exactAcyclic_walkingParallelPair_limitClosure_of_directLeftAlgebraic
      hrightOpen hrightSurj)

/-- Machine-readable state for the WPP limit transfer bridge. -/
structure DirectWppLimitFiniteShapeTransferState : Type where
  seed : String
  provedConsumer : String
  pendingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible state for the WPP limit transfer bridge. -/
def currentDirectWppLimitFiniteShapeTransferState :
    DirectWppLimitFiniteShapeTransferState where
  seed := "w541-direct-wpp-limit-finite-shape-transfer"
  provedConsumer := "directWalkingParallelPairLimitStability_of_comparison_and_limitClosure"
  pendingInputs :=
    ["mapping-cone WPP limit comparison",
      "WPP exact-acyclic limit closure"]
  productSuccessClaimed := false

theorem currentDirectWppLimitFiniteShapeTransferState_productSuccess :
    currentDirectWppLimitFiniteShapeTransferState.productSuccessClaimed = false := rfl

end DirectWppLimitFiniteShapeTransfer

namespace Dbounded

open DirectWppLimitFiniteShapeTransfer
open DirectWppOpColimitFiniteShapeTransfer
open WppOpExactAcyclicFrontierConsolidatedW318

abbrev MetrizableWppLimitComparisonInput : Prop :=
  DirectWppLimitFiniteShapeTransfer.mappingCone_boundedInclusion_walkingParallelPair_limitComparison

abbrev MetrizableWppLimitConeComparisonInput : Prop :=
  DirectWppLimitFiniteShapeTransfer.mappingCone_walkingParallelPair_limitConeComparison

abbrev MetrizableWppLimitCanonicalConeComparisonInput : Prop :=
  DirectWppLimitFiniteShapeTransfer.mappingCone_walkingParallelPair_limitCanonicalConeComparison

abbrev MetrizableWppLimitCanonicalConeDegreewiseComparisonInput : Prop :=
  DirectWppLimitFiniteShapeTransfer.mappingCone_walkingParallelPair_limitCanonicalConeDegreewiseComparison

abbrev MetrizableWppLimitClosureInput : Prop :=
  DirectWppLimitFiniteShapeTransfer.exactAcyclic_metrizableLCA_walkingParallelPair_limitClosure

abbrev MetrizableWppLimitLeftClosedInput : Prop :=
  DirectWppLimitFiniteShapeTransfer.wppLimit_preserves_leftClosedEmbedding

abbrev MetrizableWppLimitLeftClosedLcaInput : Prop :=
  DirectWppLimitFiniteShapeTransfer.wppLimit_lca_limitMap_injective_inducing_closedImage

abbrev MetrizableWppLimitRightOpenInput : Prop :=
  DirectWppLimitFiniteShapeTransfer.wppLimit_preserves_rightOpenMap

abbrev MetrizableWppLimitRightOpenLcaInput : Prop :=
  DirectWppLimitFiniteShapeTransfer.wppLimit_lca_limitMap_preserves_openMap

abbrev MetrizableWppLimitRightSurjectiveInput : Prop :=
  DirectWppLimitFiniteShapeTransfer.rightSurjective_walkingParallelPair_limitClosure

abbrev MetrizableWppLimitRightSurjectiveLcaInput : Prop :=
  DirectWppLimitFiniteShapeTransfer.wppLimit_lca_limitMap_preserves_surjective

abbrev MetrizableWppLimitRightSurjectiveZeroCorrectionBoundary : Prop :=
  DirectWppLimitFiniteShapeTransfer.rightSurjective_walkingParallelPair_limitZeroCorrectionBoundary

abbrev MetrizableWppLimitRightSurjectiveDifferenceCorrectionBoundary : Prop :=
  DirectWppLimitFiniteShapeTransfer.rightSurjective_walkingParallelPair_limitDifferenceCorrectionBoundary

abbrev MetrizableWppLimitRightSurjectiveSourceDifferenceSurjectiveBoundary : Prop :=
  rightSurjective_walkingParallelPair_limitSourceDifferenceSurjectiveBoundary

abbrev MetrizableWppLimitAlgebraicExactInput : Prop :=
  DirectWppLimitFiniteShapeTransfer.algebraicExact_walkingParallelPair_limitClosure

abbrev MetrizableWppLimitAlgebraicExactLcaInput : Prop :=
  DirectWppLimitFiniteShapeTransfer.wppLimit_lca_limitShortComplex_algebraicExact

abbrev MetrizableWppOpExactAcyclicClosureInput : Prop :=
  exactAcyclic_metrizableLCA_walkingParallelPairOp_colimitClosure

abbrev MetrizableWppOpLeftClosedInput : Prop :=
  wppOp_lca_colimitMap_injective_inducing_closedImage

abbrev MetrizableWppOpSnakeInput : Prop :=
  addCommGrpStrictSnakeCokernel_wppOp_colimit_boundary_for_metrizable

/-- Build the WPP limit left closed-embedding field from a pure LCA map certificate. -/
theorem metrizableWppLimitLeftClosedInput_of_lca
    (hlimit : MetrizableWppLimitLeftClosedLcaInput) :
    MetrizableWppLimitLeftClosedInput :=
  wppLimit_preserves_leftClosedEmbedding_of_injective_inducing_closedImage hlimit

/-- The direct WPP equalizer argument supplies the pure LCA left closed-embedding input. -/
theorem metrizableWppLimitLeftClosedLcaInput_direct :
    MetrizableWppLimitLeftClosedLcaInput :=
  wppLimit_lca_limitMap_injective_inducing_closedImage_direct

/-- The direct WPP equalizer argument supplies the left closed-embedding field. -/
theorem metrizableWppLimitLeftClosedInput_direct :
    MetrizableWppLimitLeftClosedInput :=
  metrizableWppLimitLeftClosedInput_of_lca
    metrizableWppLimitLeftClosedLcaInput_direct

/-- Build the WPP limit right open-map field from a pure LCA map certificate. -/
theorem metrizableWppLimitRightOpenInput_of_lca
    (hlimit : MetrizableWppLimitRightOpenLcaInput) :
    MetrizableWppLimitRightOpenInput :=
  wppLimit_preserves_rightOpenMap_of_lca_limitMap hlimit

/-- Build the WPP limit right-surjectivity field from a pure LCA map certificate. -/
theorem metrizableWppLimitRightSurjectiveInput_of_lca
    (hlimit : MetrizableWppLimitRightSurjectiveLcaInput) :
    MetrizableWppLimitRightSurjectiveInput :=
  rightSurjective_walkingParallelPair_limitClosure_of_lca_limitMap hlimit

/--
Build the WPP limit right-surjectivity field from zero-component correction data.
-/
theorem metrizableWppLimitRightSurjectiveInput_of_zeroCorrectionBoundary
    (hboundary : MetrizableWppLimitRightSurjectiveZeroCorrectionBoundary) :
    MetrizableWppLimitRightSurjectiveInput :=
  rightSurjective_walkingParallelPair_limitClosure_of_zeroCorrectionBoundary hboundary

/--
Build the zero-component correction boundary from difference-form correction
data.
-/
theorem metrizableWppLimitRightSurjectiveZeroCorrectionBoundary_of_differenceCorrectionBoundary
    (hboundary : MetrizableWppLimitRightSurjectiveDifferenceCorrectionBoundary) :
    MetrizableWppLimitRightSurjectiveZeroCorrectionBoundary :=
  rightSurjective_walkingParallelPair_limitZeroCorrectionBoundary_of_differenceCorrectionBoundary
    hboundary

/--
Build the difference-form correction boundary from source-difference
surjectivity.
-/
theorem
    metrizableWppLimitRightSurjectiveDifferenceCorrectionBoundary_of_sourceDifferenceSurjectiveBoundary
    (hboundary :
      MetrizableWppLimitRightSurjectiveSourceDifferenceSurjectiveBoundary) :
    MetrizableWppLimitRightSurjectiveDifferenceCorrectionBoundary :=
  rightSurjective_walkingParallelPair_limitDifferenceCorrectionBoundary_of_sourceDifferenceSurjectiveBoundary
    hboundary

/--
Build the WPP limit right-surjectivity field from difference-form correction
data.
-/
theorem metrizableWppLimitRightSurjectiveInput_of_differenceCorrectionBoundary
    (hboundary : MetrizableWppLimitRightSurjectiveDifferenceCorrectionBoundary) :
    MetrizableWppLimitRightSurjectiveInput :=
  rightSurjective_walkingParallelPair_limitClosure_of_differenceCorrectionBoundary hboundary

/--
Build the WPP limit right-surjectivity field from source-difference
surjectivity.
-/
theorem metrizableWppLimitRightSurjectiveInput_of_sourceDifferenceSurjectiveBoundary
    (hboundary :
      MetrizableWppLimitRightSurjectiveSourceDifferenceSurjectiveBoundary) :
    MetrizableWppLimitRightSurjectiveInput :=
  rightSurjective_walkingParallelPair_limitClosure_of_sourceDifferenceSurjectiveBoundary
    hboundary

/-- Build the WPP limit algebraic-exactness field from component limit data. -/
theorem metrizableWppLimitAlgebraicExactInput_of_lca
    (hlimit : MetrizableWppLimitAlgebraicExactLcaInput) :
    MetrizableWppLimitAlgebraicExactInput :=
  algebraicExact_walkingParallelPair_limitClosure_of_lca_limitShortComplex hlimit

/-- The direct WPP equalizer argument supplies algebraic exactness at WPP limits. -/
theorem metrizableWppLimitAlgebraicExactInput_direct :
    MetrizableWppLimitAlgebraicExactInput :=
  algebraicExact_walkingParallelPair_limitClosure_direct

/-- Build the WPP limit comparison input from a fixed mapping-cone diagram cone input. -/
theorem metrizableWppLimitComparisonInput_of_limitConeComparison
    (hcomparison : MetrizableWppLimitConeComparisonInput) :
    MetrizableWppLimitComparisonInput :=
  mappingCone_boundedInclusion_walkingParallelPair_limitComparison_of_limitConeComparison
    hcomparison

/-- Build the WPP cone-comparison input from the canonical mapping-cone cone. -/
theorem metrizableWppLimitConeComparisonInput_of_canonicalCone
    (hcomparison : MetrizableWppLimitCanonicalConeComparisonInput) :
    MetrizableWppLimitConeComparisonInput :=
  mappingCone_walkingParallelPair_limitConeComparison_of_canonicalCone hcomparison

/-- Build the canonical cone comparison input from degreewise limit proofs. -/
theorem metrizableWppLimitCanonicalConeComparisonInput_of_degreewise
    (hcomparison : MetrizableWppLimitCanonicalConeDegreewiseComparisonInput) :
    MetrizableWppLimitCanonicalConeComparisonInput :=
  mappingCone_walkingParallelPair_limitCanonicalConeComparison_of_degreewise hcomparison

/-- The W551 proof is the direct degreewise canonical cone comparison input. -/
theorem metrizableWppLimitCanonicalConeDegreewiseComparisonInput_direct :
    MetrizableWppLimitCanonicalConeDegreewiseComparisonInput :=
  mappingCone_walkingParallelPair_limitCanonicalConeDegreewiseComparison_direct

/-- The W551 proof supplies the canonical cone comparison input. -/
theorem metrizableWppLimitCanonicalConeComparisonInput_direct :
    MetrizableWppLimitCanonicalConeComparisonInput :=
  mappingCone_walkingParallelPair_limitCanonicalConeComparison_direct

/-- The W551 proof supplies the fixed mapping-cone diagram cone comparison input. -/
theorem metrizableWppLimitConeComparisonInput_direct :
    MetrizableWppLimitConeComparisonInput :=
  mappingCone_walkingParallelPair_limitConeComparison_direct

/-- The W551 proof supplies the full WPP mapping-cone comparison input. -/
theorem metrizableWppLimitComparisonInput_direct :
    MetrizableWppLimitComparisonInput :=
  mappingCone_boundedInclusion_walkingParallelPair_limitComparison_direct

/-- Four short-complex field inputs for WPP exact-acyclic limit closure. -/
structure MetrizableWalkingParallelPairLimitClosureFieldInputs : Type 1 where
  leftClosed : MetrizableWppLimitLeftClosedInput
  rightOpen : MetrizableWppLimitRightOpenInput
  rightSurjective : MetrizableWppLimitRightSurjectiveInput
  algebraicExact : MetrizableWppLimitAlgebraicExactInput

/-- Four limit-closure fields with the left field supplied by a pure LCA certificate. -/
structure MetrizableWalkingParallelPairLimitClosureFieldInputsFromLeftLca :
    Type 1 where
  leftClosedLca : MetrizableWppLimitLeftClosedLcaInput
  rightOpen : MetrizableWppLimitRightOpenInput
  rightSurjective : MetrizableWppLimitRightSurjectiveInput
  algebraicExact : MetrizableWppLimitAlgebraicExactInput

/-- Four limit-closure fields with the left and right-open fields from pure LCA data. -/
structure MetrizableWalkingParallelPairLimitClosureFieldInputsFromLeftRightLca :
    Type 1 where
  leftClosedLca : MetrizableWppLimitLeftClosedLcaInput
  rightOpenLca : MetrizableWppLimitRightOpenLcaInput
  rightSurjective : MetrizableWppLimitRightSurjectiveInput
  algebraicExact : MetrizableWppLimitAlgebraicExactInput

/-- Four limit-closure fields with the first three fields from pure LCA data. -/
structure MetrizableWalkingParallelPairLimitClosureFieldInputsFromLeftRightSurjLca :
    Type 1 where
  leftClosedLca : MetrizableWppLimitLeftClosedLcaInput
  rightOpenLca : MetrizableWppLimitRightOpenLcaInput
  rightSurjectiveLca : MetrizableWppLimitRightSurjectiveLcaInput
  algebraicExact : MetrizableWppLimitAlgebraicExactInput

/-- Four limit-closure fields supplied by LCA/component limit certificates. -/
structure MetrizableWalkingParallelPairLimitClosureFieldInputsFromAllLca :
    Type 1 where
  leftClosedLca : MetrizableWppLimitLeftClosedLcaInput
  rightOpenLca : MetrizableWppLimitRightOpenLcaInput
  rightSurjectiveLca : MetrizableWppLimitRightSurjectiveLcaInput
  algebraicExactLca : MetrizableWppLimitAlgebraicExactLcaInput

/--
WPP limit-closure fields with the left closed-embedding and algebraic exactness
fields supplied by direct equalizer arguments. Only the two right-field inputs
remain.
-/
structure MetrizableWalkingParallelPairLimitClosureFieldInputsFromDirectLeftAlgebraic :
    Type 1 where
  rightOpen : MetrizableWppLimitRightOpenInput
  rightSurjective : MetrizableWppLimitRightSurjectiveInput

/--
WPP limit-closure fields with direct left/algebraic proofs and pure LCA
right-side fields.
-/
structure MetrizableWalkingParallelPairLimitClosureFieldInputsFromDirectLeftAlgebraicRightLca :
    Type 1 where
  rightOpenLca : MetrizableWppLimitRightOpenLcaInput
  rightSurjectiveLca : MetrizableWppLimitRightSurjectiveLcaInput

/-- Build the four WPP limit-closure field inputs from a pure LCA left field. -/
def metrizableWalkingParallelPairLimitClosureFieldInputs_of_leftLca
    (inputs : MetrizableWalkingParallelPairLimitClosureFieldInputsFromLeftLca) :
    MetrizableWalkingParallelPairLimitClosureFieldInputs where
  leftClosed := metrizableWppLimitLeftClosedInput_of_lca inputs.leftClosedLca
  rightOpen := inputs.rightOpen
  rightSurjective := inputs.rightSurjective
  algebraicExact := inputs.algebraicExact

/-- Build the four WPP limit-closure fields from pure LCA left and right-open data. -/
def metrizableWalkingParallelPairLimitClosureFieldInputs_of_leftRightLca
    (inputs : MetrizableWalkingParallelPairLimitClosureFieldInputsFromLeftRightLca) :
    MetrizableWalkingParallelPairLimitClosureFieldInputs where
  leftClosed := metrizableWppLimitLeftClosedInput_of_lca inputs.leftClosedLca
  rightOpen := metrizableWppLimitRightOpenInput_of_lca inputs.rightOpenLca
  rightSurjective := inputs.rightSurjective
  algebraicExact := inputs.algebraicExact

/-- Build the four WPP limit-closure fields from the first three pure LCA fields. -/
def metrizableWalkingParallelPairLimitClosureFieldInputs_of_leftRightSurjLca
    (inputs :
      MetrizableWalkingParallelPairLimitClosureFieldInputsFromLeftRightSurjLca) :
    MetrizableWalkingParallelPairLimitClosureFieldInputs where
  leftClosed := metrizableWppLimitLeftClosedInput_of_lca inputs.leftClosedLca
  rightOpen := metrizableWppLimitRightOpenInput_of_lca inputs.rightOpenLca
  rightSurjective :=
    metrizableWppLimitRightSurjectiveInput_of_lca inputs.rightSurjectiveLca
  algebraicExact := inputs.algebraicExact

/-- Build the four WPP limit-closure fields from LCA/component certificates. -/
def metrizableWalkingParallelPairLimitClosureFieldInputs_of_allLca
    (inputs : MetrizableWalkingParallelPairLimitClosureFieldInputsFromAllLca) :
    MetrizableWalkingParallelPairLimitClosureFieldInputs where
  leftClosed := metrizableWppLimitLeftClosedInput_of_lca inputs.leftClosedLca
  rightOpen := metrizableWppLimitRightOpenInput_of_lca inputs.rightOpenLca
  rightSurjective :=
    metrizableWppLimitRightSurjectiveInput_of_lca inputs.rightSurjectiveLca
  algebraicExact :=
    metrizableWppLimitAlgebraicExactInput_of_lca inputs.algebraicExactLca

/-- Build the WPP limit-closure fields from direct left and algebraic proofs. -/
def metrizableWalkingParallelPairLimitClosureFieldInputs_of_directLeftAlgebraic
    (inputs : MetrizableWalkingParallelPairLimitClosureFieldInputsFromDirectLeftAlgebraic) :
    MetrizableWalkingParallelPairLimitClosureFieldInputs where
  leftClosed := metrizableWppLimitLeftClosedInput_direct
  rightOpen := inputs.rightOpen
  rightSurjective := inputs.rightSurjective
  algebraicExact := metrizableWppLimitAlgebraicExactInput_direct

/--
Build the WPP limit-closure fields from direct left/algebraic proofs and pure
LCA right-side certificates.
-/
def metrizableWalkingParallelPairLimitClosureFieldInputs_of_directLeftAlgebraicRightLca
    (inputs :
      MetrizableWalkingParallelPairLimitClosureFieldInputsFromDirectLeftAlgebraicRightLca) :
    MetrizableWalkingParallelPairLimitClosureFieldInputs where
  leftClosed := metrizableWppLimitLeftClosedInput_direct
  rightOpen := metrizableWppLimitRightOpenInput_of_lca inputs.rightOpenLca
  rightSurjective :=
    metrizableWppLimitRightSurjectiveInput_of_lca inputs.rightSurjectiveLca
  algebraicExact := metrizableWppLimitAlgebraicExactInput_direct

/-- Build WPP exact-acyclic limit closure from the four short-complex field inputs. -/
theorem metrizableWalkingParallelPairLimitClosure_of_fieldInputs
    (inputs : MetrizableWalkingParallelPairLimitClosureFieldInputs) :
    MetrizableWppLimitClosureInput :=
  exactAcyclic_walkingParallelPair_limitClosure_of_fields
    inputs.leftClosed
    inputs.rightOpen
    inputs.rightSurjective
    inputs.algebraicExact

/-- Build WPP exact-acyclic limit closure when the left field comes from pure LCA data. -/
theorem metrizableWalkingParallelPairLimitClosure_of_leftLca
    (inputs : MetrizableWalkingParallelPairLimitClosureFieldInputsFromLeftLca) :
    MetrizableWppLimitClosureInput :=
  metrizableWalkingParallelPairLimitClosure_of_fieldInputs
    (metrizableWalkingParallelPairLimitClosureFieldInputs_of_leftLca inputs)

/-- Build WPP exact-acyclic limit closure from pure LCA left and right-open data. -/
theorem metrizableWalkingParallelPairLimitClosure_of_leftRightLca
    (inputs : MetrizableWalkingParallelPairLimitClosureFieldInputsFromLeftRightLca) :
    MetrizableWppLimitClosureInput :=
  metrizableWalkingParallelPairLimitClosure_of_fieldInputs
    (metrizableWalkingParallelPairLimitClosureFieldInputs_of_leftRightLca inputs)

/-- Build WPP exact-acyclic limit closure from the first three pure LCA fields. -/
theorem metrizableWalkingParallelPairLimitClosure_of_leftRightSurjLca
    (inputs :
      MetrizableWalkingParallelPairLimitClosureFieldInputsFromLeftRightSurjLca) :
    MetrizableWppLimitClosureInput :=
  metrizableWalkingParallelPairLimitClosure_of_fieldInputs
    (metrizableWalkingParallelPairLimitClosureFieldInputs_of_leftRightSurjLca inputs)

/-- Build WPP exact-acyclic limit closure from LCA/component certificates. -/
theorem metrizableWalkingParallelPairLimitClosure_of_allLca
    (inputs : MetrizableWalkingParallelPairLimitClosureFieldInputsFromAllLca) :
    MetrizableWppLimitClosureInput :=
  metrizableWalkingParallelPairLimitClosure_of_fieldInputs
    (metrizableWalkingParallelPairLimitClosureFieldInputs_of_allLca inputs)

/-- Build WPP exact-acyclic limit closure from direct left/algebraic fields. -/
theorem metrizableWalkingParallelPairLimitClosure_of_directLeftAlgebraic
    (inputs : MetrizableWalkingParallelPairLimitClosureFieldInputsFromDirectLeftAlgebraic) :
    MetrizableWppLimitClosureInput :=
  exactAcyclic_walkingParallelPair_limitClosure_of_directLeftAlgebraic
    inputs.rightOpen inputs.rightSurjective

/--
Build WPP exact-acyclic limit closure from direct left/algebraic proofs and pure
LCA right-side certificates.
-/
theorem metrizableWalkingParallelPairLimitClosure_of_directLeftAlgebraicRightLca
    (inputs :
      MetrizableWalkingParallelPairLimitClosureFieldInputsFromDirectLeftAlgebraicRightLca) :
    MetrizableWppLimitClosureInput :=
  metrizableWalkingParallelPairLimitClosure_of_directLeftAlgebraic
    { rightOpen := metrizableWppLimitRightOpenInput_of_lca inputs.rightOpenLca
      rightSurjective :=
        metrizableWppLimitRightSurjectiveInput_of_lca inputs.rightSurjectiveLca }

theorem metrizableWalkingParallelPairLimitStability_of_comparison_and_closure
    (hcomparison : MetrizableWppLimitComparisonInput)
    (hclosure : MetrizableWppLimitClosureInput) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair :=
  directWalkingParallelPairLimitStability_of_comparison_and_limitClosure
    hcomparison hclosure

/-- Build WPP limit stability from comparison and short-complex closure fields. -/
theorem metrizableWalkingParallelPairLimitStability_of_comparison_and_fields
    (hcomparison : MetrizableWppLimitComparisonInput)
    (inputs : MetrizableWalkingParallelPairLimitClosureFieldInputs) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair :=
  directWalkingParallelPairLimitStability_of_comparison_and_limitFields
    hcomparison
    inputs.leftClosed
    inputs.rightOpen
    inputs.rightSurjective
    inputs.algebraicExact

/-- Build WPP limit stability when the left field comes from pure LCA data. -/
theorem metrizableWalkingParallelPairLimitStability_of_comparison_and_leftLca
    (hcomparison : MetrizableWppLimitComparisonInput)
    (inputs : MetrizableWalkingParallelPairLimitClosureFieldInputsFromLeftLca) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair :=
  metrizableWalkingParallelPairLimitStability_of_comparison_and_fields
    hcomparison
    (metrizableWalkingParallelPairLimitClosureFieldInputs_of_leftLca inputs)

/-- Build WPP limit stability from comparison plus pure LCA left and right-open data. -/
theorem metrizableWalkingParallelPairLimitStability_of_comparison_and_leftRightLca
    (hcomparison : MetrizableWppLimitComparisonInput)
    (inputs : MetrizableWalkingParallelPairLimitClosureFieldInputsFromLeftRightLca) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair :=
  metrizableWalkingParallelPairLimitStability_of_comparison_and_fields
    hcomparison
    (metrizableWalkingParallelPairLimitClosureFieldInputs_of_leftRightLca inputs)

/-- Build WPP limit stability from comparison plus the first three pure LCA fields. -/
theorem metrizableWalkingParallelPairLimitStability_of_comparison_and_leftRightSurjLca
    (hcomparison : MetrizableWppLimitComparisonInput)
    (inputs :
      MetrizableWalkingParallelPairLimitClosureFieldInputsFromLeftRightSurjLca) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair :=
  metrizableWalkingParallelPairLimitStability_of_comparison_and_fields
    hcomparison
    (metrizableWalkingParallelPairLimitClosureFieldInputs_of_leftRightSurjLca inputs)

/-- Build WPP limit stability from comparison plus LCA/component field data. -/
theorem metrizableWalkingParallelPairLimitStability_of_comparison_and_allLca
    (hcomparison : MetrizableWppLimitComparisonInput)
    (inputs : MetrizableWalkingParallelPairLimitClosureFieldInputsFromAllLca) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair :=
  metrizableWalkingParallelPairLimitStability_of_comparison_and_fields
    hcomparison
    (metrizableWalkingParallelPairLimitClosureFieldInputs_of_allLca inputs)

/-- Build WPP limit stability from direct comparison plus direct left/algebraic fields. -/
theorem metrizableWalkingParallelPairLimitStability_of_comparison_and_directLeftAlgebraic
    (hcomparison : MetrizableWppLimitComparisonInput)
    (inputs : MetrizableWalkingParallelPairLimitClosureFieldInputsFromDirectLeftAlgebraic) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair :=
  directWalkingParallelPairLimitStability_of_comparison_and_directLeftAlgebraic
    hcomparison inputs.rightOpen inputs.rightSurjective

/--
Build WPP limit stability from comparison, direct left/algebraic proofs, and
pure LCA right-side certificates.
-/
theorem metrizableWalkingParallelPairLimitStability_of_comparison_and_directLeftAlgebraicRightLca
    (hcomparison : MetrizableWppLimitComparisonInput)
    (inputs :
      MetrizableWalkingParallelPairLimitClosureFieldInputsFromDirectLeftAlgebraicRightLca) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair :=
  metrizableWalkingParallelPairLimitStability_of_comparison_and_directLeftAlgebraic
    hcomparison
    { rightOpen := metrizableWppLimitRightOpenInput_of_lca inputs.rightOpenLca
      rightSurjective :=
        metrizableWppLimitRightSurjectiveInput_of_lca inputs.rightSurjectiveLca }

/-- Build WPP limit stability from fixed cone comparison plus LCA/component field data. -/
theorem metrizableWalkingParallelPairLimitStability_of_limitConeComparison_and_allLca
    (hcomparison : MetrizableWppLimitConeComparisonInput)
    (inputs : MetrizableWalkingParallelPairLimitClosureFieldInputsFromAllLca) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair :=
  metrizableWalkingParallelPairLimitStability_of_comparison_and_allLca
    (metrizableWppLimitComparisonInput_of_limitConeComparison hcomparison)
    inputs

/-- Build WPP limit stability from canonical cone comparison plus LCA/component data. -/
theorem metrizableWalkingParallelPairLimitStability_of_canonicalConeComparison_and_allLca
    (hcomparison : MetrizableWppLimitCanonicalConeComparisonInput)
    (inputs : MetrizableWalkingParallelPairLimitClosureFieldInputsFromAllLca) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair :=
  metrizableWalkingParallelPairLimitStability_of_limitConeComparison_and_allLca
    (metrizableWppLimitConeComparisonInput_of_canonicalCone hcomparison)
    inputs

/-- Build WPP limit stability from degreewise canonical cone limits plus LCA/component data. -/
theorem metrizableWalkingParallelPairLimitStability_of_degreewiseConeComparison_and_allLca
    (hcomparison : MetrizableWppLimitCanonicalConeDegreewiseComparisonInput)
    (inputs : MetrizableWalkingParallelPairLimitClosureFieldInputsFromAllLca) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair :=
  metrizableWalkingParallelPairLimitStability_of_canonicalConeComparison_and_allLca
    (metrizableWppLimitCanonicalConeComparisonInput_of_degreewise hcomparison)
    inputs

/-- Build WPP limit stability from the W551 direct comparison and LCA/component data. -/
theorem metrizableWalkingParallelPairLimitStability_of_allLca
    (inputs : MetrizableWalkingParallelPairLimitClosureFieldInputsFromAllLca) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair :=
  metrizableWalkingParallelPairLimitStability_of_comparison_and_allLca
    metrizableWppLimitComparisonInput_direct inputs

/-- Build WPP limit stability from W551 comparison plus direct left/algebraic fields. -/
theorem metrizableWalkingParallelPairLimitStability_of_directLeftAlgebraic
    (inputs : MetrizableWalkingParallelPairLimitClosureFieldInputsFromDirectLeftAlgebraic) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair :=
  metrizableWalkingParallelPairLimitStability_of_comparison_and_directLeftAlgebraic
    metrizableWppLimitComparisonInput_direct inputs

/--
Build WPP limit stability from W551/W555 direct left/algebraic proofs and pure
LCA right-side certificates.
-/
theorem metrizableWalkingParallelPairLimitStability_of_directLeftAlgebraicRightLca
    (inputs :
      MetrizableWalkingParallelPairLimitClosureFieldInputsFromDirectLeftAlgebraicRightLca) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair :=
  metrizableWalkingParallelPairLimitStability_of_comparison_and_directLeftAlgebraicRightLca
    metrizableWppLimitComparisonInput_direct inputs

/--
W532 finite-shape transfer inputs with WPP limit stability supplied by direct
limit comparison and WPP colimit stability supplied by WPP-op closure.
-/
structure MetrizableWalkingParallelPairFiniteShapeTransferInputsFromLimitAndOpClosure :
    Type 1 where
  limitComparison : MetrizableWppLimitComparisonInput
  limitClosure : MetrizableWppLimitClosureInput
  opExactAcyclicClosure : MetrizableWppOpExactAcyclicClosureInput
  functorCategoryLocalization :
    Dbounded.MetrizableWalkingParallelPairFunctorCategoryLocalizationInput

/-- Build W532's transfer record from direct WPP limit data and WPP-op colimit closure. -/
noncomputable def
    metrizableWalkingParallelPairFiniteShapeTransferInputs_of_limitAndOpClosure
    (inputs : MetrizableWalkingParallelPairFiniteShapeTransferInputsFromLimitAndOpClosure) :
    Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs where
  limitStability :=
    metrizableWalkingParallelPairLimitStability_of_comparison_and_closure
      inputs.limitComparison
      inputs.limitClosure
  colimitStability :=
    DirectWppOpColimitFiniteShapeTransfer.walkingParallelPairColimitStability_of_exactAcyclicClosure
      inputs.opExactAcyclicClosure
  functorCategoryLocalization := inputs.functorCategoryLocalization

/--
W532 finite-shape transfer inputs with WPP limit stability supplied by direct
limit comparison and WPP colimit stability supplied by the left/Snake route.
-/
structure MetrizableWalkingParallelPairFiniteShapeTransferInputsFromLimitAndLeftSnake :
    Type 1 where
  limitComparison : MetrizableWppLimitComparisonInput
  limitClosure : MetrizableWppLimitClosureInput
  leftClosed : MetrizableWppOpLeftClosedInput
  snake : MetrizableWppOpSnakeInput
  functorCategoryLocalization :
    Dbounded.MetrizableWalkingParallelPairFunctorCategoryLocalizationInput

/-- Build W532's transfer record from direct WPP limit data and the left/Snake route. -/
noncomputable def
    metrizableWalkingParallelPairFiniteShapeTransferInputs_of_limitAndLeftSnake
    (inputs : MetrizableWalkingParallelPairFiniteShapeTransferInputsFromLimitAndLeftSnake) :
    Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs where
  limitStability :=
    metrizableWalkingParallelPairLimitStability_of_comparison_and_closure
      inputs.limitComparison
      inputs.limitClosure
  colimitStability :=
    walkingParallelPairColimitStability_of_left_and_snakeCokernel
      inputs.leftClosed inputs.snake
  functorCategoryLocalization := inputs.functorCategoryLocalization

/-- Input names for the direct-limit plus WPP-op closure form of W532 finite-shape transfer. -/
def
    metrizableWalkingParallelPairFiniteShapeTransferFromLimitAndOpClosureInputNames :
    List String :=
  ["mapping-cone WPP limit comparison",
    "WPP exact-acyclic limit closure",
    "WPP-op exact-acyclic colimit closure",
    "WalkingParallelPair functor-category localization"]

theorem
    metrizableWalkingParallelPairFiniteShapeTransferFromLimitAndOpClosureInputNames_count :
    metrizableWalkingParallelPairFiniteShapeTransferFromLimitAndOpClosureInputNames.length = 4 :=
  rfl

/-- Input names for the direct-limit plus left/Snake form of W532 finite-shape transfer. -/
def
    metrizableWalkingParallelPairFiniteShapeTransferFromLimitAndLeftSnakeInputNames :
    List String :=
  ["mapping-cone WPP limit comparison",
    "WPP exact-acyclic limit closure",
    "WPP-op colimit left closed-embedding certificate",
    "WPP-op AddCommGrp SnakeInput cokernel-row certificate",
    "WalkingParallelPair functor-category localization"]

theorem
    metrizableWalkingParallelPairFiniteShapeTransferFromLimitAndLeftSnakeInputNames_count :
    metrizableWalkingParallelPairFiniteShapeTransferFromLimitAndLeftSnakeInputNames.length = 5 :=
  rfl

/--
W532 finite-shape transfer inputs with WPP limit closure supplied by four
short-complex field inputs and WPP colimit stability supplied by WPP-op closure.
-/
structure MetrizableWalkingParallelPairFiniteShapeTransferInputsFromLimitFieldsAndOpClosure :
    Type 1 where
  limitComparison : MetrizableWppLimitComparisonInput
  limitFields : MetrizableWalkingParallelPairLimitClosureFieldInputs
  opExactAcyclicClosure : MetrizableWppOpExactAcyclicClosureInput
  functorCategoryLocalization :
    Dbounded.MetrizableWalkingParallelPairFunctorCategoryLocalizationInput

/-- Build W532's transfer record from direct WPP limit fields and WPP-op closure. -/
noncomputable def
    metrizableWalkingParallelPairFiniteShapeTransferInputs_of_limitFieldsAndOpClosure
    (inputs :
      MetrizableWalkingParallelPairFiniteShapeTransferInputsFromLimitFieldsAndOpClosure) :
    Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs where
  limitStability :=
    metrizableWalkingParallelPairLimitStability_of_comparison_and_fields
      inputs.limitComparison
      inputs.limitFields
  colimitStability :=
    DirectWppOpColimitFiniteShapeTransfer.walkingParallelPairColimitStability_of_exactAcyclicClosure
      inputs.opExactAcyclicClosure
  functorCategoryLocalization := inputs.functorCategoryLocalization

/--
W532 finite-shape transfer inputs with WPP limit closure supplied by four
short-complex field inputs and WPP colimit stability supplied by the left/Snake route.
-/
structure MetrizableWalkingParallelPairFiniteShapeTransferInputsFromLimitFieldsAndLeftSnake :
    Type 1 where
  limitComparison : MetrizableWppLimitComparisonInput
  limitFields : MetrizableWalkingParallelPairLimitClosureFieldInputs
  leftClosed : MetrizableWppOpLeftClosedInput
  snake : MetrizableWppOpSnakeInput
  functorCategoryLocalization :
    Dbounded.MetrizableWalkingParallelPairFunctorCategoryLocalizationInput

/-- Build W532's transfer record from direct WPP limit fields and the left/Snake route. -/
noncomputable def
    metrizableWalkingParallelPairFiniteShapeTransferInputs_of_limitFieldsAndLeftSnake
    (inputs :
      MetrizableWalkingParallelPairFiniteShapeTransferInputsFromLimitFieldsAndLeftSnake) :
    Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs where
  limitStability :=
    metrizableWalkingParallelPairLimitStability_of_comparison_and_fields
      inputs.limitComparison
      inputs.limitFields
  colimitStability :=
    walkingParallelPairColimitStability_of_left_and_snakeCokernel
      inputs.leftClosed inputs.snake
  functorCategoryLocalization := inputs.functorCategoryLocalization

/-- Input names for the direct-limit-field plus WPP-op closure transfer form. -/
def
    metrizableWalkingParallelPairFiniteShapeTransferFromLimitFieldsAndOpClosureInputNames :
    List String :=
  ["mapping-cone WPP limit comparison",
    "WPP limit left closed-embedding field",
    "WPP limit right open-map field",
    "WPP limit right-surjectivity field",
    "WPP limit algebraic exactness field",
    "WPP-op exact-acyclic colimit closure",
    "WalkingParallelPair functor-category localization"]

theorem
    metrizableWalkingParallelPairFiniteShapeTransferFromLimitFieldsAndOpClosureInputNames_count :
    metrizableWalkingParallelPairFiniteShapeTransferFromLimitFieldsAndOpClosureInputNames.length =
      7 :=
  rfl

/-- Input names for the direct-limit-field plus left/Snake transfer form. -/
def
    metrizableWalkingParallelPairFiniteShapeTransferFromLimitFieldsAndLeftSnakeInputNames :
    List String :=
  ["mapping-cone WPP limit comparison",
    "WPP limit left closed-embedding field",
    "WPP limit right open-map field",
    "WPP limit right-surjectivity field",
    "WPP limit algebraic exactness field",
    "WPP-op colimit left closed-embedding certificate",
    "WPP-op AddCommGrp SnakeInput cokernel-row certificate",
    "WalkingParallelPair functor-category localization"]

theorem
    metrizableWalkingParallelPairFiniteShapeTransferFromLimitFieldsAndLeftSnakeInputNames_count :
    metrizableWalkingParallelPairFiniteShapeTransferFromLimitFieldsAndLeftSnakeInputNames.length =
      8 :=
  rfl

end Dbounded

end LeanLCAExactChallenge
