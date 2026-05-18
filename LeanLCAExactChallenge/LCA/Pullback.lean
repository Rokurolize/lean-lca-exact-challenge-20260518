import LeanLCAExactChallenge.LCA.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Constructions

/-!
Explicit pullbacks in the local `MetrizableLCA` category.

The pullback of continuous additive homomorphisms is realised as the closed
additive subgroup of the product cut out by the equality relation.
-/

set_option autoImplicit false

universe u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace MetrizableLCA

variable {A B C : MetrizableLCA.{u}} (f : A ⟶ C) (g : B ⟶ C)

/-- The additive subgroup of `A × B` underlying the explicit pullback of `f` and `g`. -/
def pullbackSubgroup : AddSubgroup (A × B) where
  carrier := {p | f p.1 = g p.2}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    calc
      f (x.1 + y.1) = f x.1 + f y.1 := (f.hom : A →+ C).map_add x.1 y.1
      _ = g x.2 + g y.2 := by rw [hx, hy]
      _ = g (x.2 + y.2) := ((g.hom : B →+ C).map_add x.2 y.2).symm
  neg_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    calc
      f (-x.1) = - f x.1 := (f.hom : A →+ C).map_neg x.1
      _ = - g x.2 := by rw [hx]
      _ = g (-x.2) := ((g.hom : B →+ C).map_neg x.2).symm

lemma pullbackSubgroup_isClosed : IsClosed (pullbackSubgroup f g : Set (A × B)) := by
  dsimp [pullbackSubgroup]
  exact isClosed_eq (f.hom.continuous.comp continuous_fst) (g.hom.continuous.comp continuous_snd)

/-- The explicit pullback object in `MetrizableLCA`. -/
def pullbackObj : MetrizableLCA.{u} where
  carrier := pullbackSubgroup f g
  locallyCompactSpace := by
    change LocallyCompactSpace {p : A × B // p ∈ (pullbackSubgroup f g : Set (A × B))}
    exact (pullbackSubgroup_isClosed f g).locallyCompactSpace
  metrizableSpace := by
    change TopologicalSpace.MetrizableSpace {p : A × B // p ∈ (pullbackSubgroup f g : Set (A × B))}
    infer_instance

/-- First projection from the explicit pullback. -/
noncomputable def pullbackFst : pullbackObj f g ⟶ A where
  hom' :=
    { toFun := fun p => p.1.1
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      continuous_toFun := continuous_subtype_val.fst }

/-- Second projection from the explicit pullback. -/
noncomputable def pullbackSnd : pullbackObj f g ⟶ B where
  hom' :=
    { toFun := fun p => p.1.2
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      continuous_toFun := continuous_subtype_val.snd }

lemma pullback_condition : pullbackFst f g ≫ f = pullbackSnd f g ≫ g := by
  ext p
  exact p.2

/-- The universal lift into the explicit pullback. -/
noncomputable def pullbackLift {X : MetrizableLCA.{u}} (a : X ⟶ A) (b : X ⟶ B)
    (w : a ≫ f = b ≫ g) : X ⟶ pullbackObj f g where
  hom' :=
    { toFun := fun x => ⟨(a x, b x), by
        exact congrArg (fun h : X ⟶ C => h x) w⟩
      map_zero' := by
        apply Subtype.ext
        calc
          ((a 0, b 0) : A × B) = 0 := by ext <;> simp
          _ = ↑(0 : pullbackSubgroup f g) := (AddSubgroup.coe_zero (pullbackSubgroup f g)).symm
      map_add' := by
        intro x y
        apply Subtype.ext
        let ux : pullbackSubgroup f g := ⟨(a x, b x), congrArg (fun h : X ⟶ C => h x) w⟩
        let uy : pullbackSubgroup f g := ⟨(a y, b y), congrArg (fun h : X ⟶ C => h y) w⟩
        calc
          ((a (x + y), b (x + y)) : A × B) = (↑ux + ↑uy : A × B) := by
            ext <;> simp [ux, uy, map_add]
          _ = ↑(ux + uy) := (AddSubgroup.coe_add (pullbackSubgroup f g) ux uy).symm
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact a.hom.continuous.prodMk b.hom.continuous }

lemma pullbackLift_fst {X : MetrizableLCA.{u}} (a : X ⟶ A) (b : X ⟶ B)
    (w : a ≫ f = b ≫ g) : pullbackLift f g a b w ≫ pullbackFst f g = a := by
  ext x
  rfl

lemma pullbackLift_snd {X : MetrizableLCA.{u}} (a : X ⟶ A) (b : X ⟶ B)
    (w : a ≫ f = b ≫ g) : pullbackLift f g a b w ≫ pullbackSnd f g = b := by
  ext x
  rfl

lemma pullback_hom_ext {X : MetrizableLCA.{u}} {k l : X ⟶ pullbackObj f g}
    (hfst : k ≫ pullbackFst f g = l ≫ pullbackFst f g)
    (hsnd : k ≫ pullbackSnd f g = l ≫ pullbackSnd f g) : k = l := by
  apply MetrizableLCA.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun h : X ⟶ A => h x) hfst
  · exact congrArg (fun h : X ⟶ B => h x) hsnd

/-- The explicit pullback cone in `MetrizableLCA`. -/
noncomputable def pullbackCone : PullbackCone f g :=
  PullbackCone.mk (pullbackFst f g) (pullbackSnd f g) (pullback_condition f g)

/-- The explicit pullback cone is limiting. -/
noncomputable def pullbackIsLimit : IsLimit (pullbackCone f g) :=
  PullbackCone.isLimitAux (pullbackCone f g)
    (fun s => pullbackLift f g s.fst s.snd s.condition)
    (fun s => pullbackLift_fst f g s.fst s.snd s.condition)
    (fun s => pullbackLift_snd f g s.fst s.snd s.condition)
    (fun s m hm => by
      apply pullback_hom_ext f g
      · exact hm WalkingCospan.left
      · exact hm WalkingCospan.right)

noncomputable instance hasPullback : HasPullback f g where
  exists_limit := ⟨⟨pullbackCone f g, pullbackIsLimit f g⟩⟩

end MetrizableLCA

end LeanLCAExactChallenge
