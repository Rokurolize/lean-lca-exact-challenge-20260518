/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import Mathlib.CategoryTheory.Enriched.Opposite

/-!
# Transporting enriched functors

This file transports enriched functors along lax monoidal functors and through enriched
opposites.
-/

set_option autoImplicit false

noncomputable section

namespace CategoryTheory

open MonoidalCategory BraidedCategory

universe v₁ v₂ u₁ u₂ u₃

variable {V : Type u₁} [Category.{v₁} V] [MonoidalCategory V]
variable {W : Type u₂} [Category.{v₂} W] [MonoidalCategory W]
variable {C : Type u₃} {D : Type u₃}

/-- Transport an enriched functor along a lax monoidal change of enriching category. -/
def EnrichedFunctor.transport
    (T : V ⥤ W) [T.LaxMonoidal]
    [EnrichedCategory V C] [EnrichedCategory V D]
    (F : EnrichedFunctor V C D) :
    EnrichedFunctor W (TransportEnrichment T C) (TransportEnrichment T D) where
  obj X := F.obj X
  map X Y := T.map (F.map X Y)
  map_id X := by
    change C at X
    change (Functor.LaxMonoidal.ε T ≫ T.map (eId V X)) ≫
        T.map (F.map X X) =
      Functor.LaxMonoidal.ε T ≫ T.map (eId V (F.obj X))
    simp only [Category.assoc, ← T.map_comp, F.map_id]
  map_comp X Y Z := by
    change C at X Y Z
    change (Functor.LaxMonoidal.μ T (X ⟶[V] Y) (Y ⟶[V] Z) ≫
          T.map (eComp V X Y Z)) ≫ T.map (F.map X Z) =
      (T.map (F.map X Y) ⊗ₘ T.map (F.map Y Z)) ≫
        Functor.LaxMonoidal.μ T _ _ ≫
          T.map (eComp V (F.obj X) (F.obj Y) (F.obj Z))
    rw [Category.assoc, ← T.map_comp, F.map_comp, T.map_comp]
    rw [Functor.LaxMonoidal.μ_natural_assoc]

variable [BraidedCategory V] [EnrichedCategory V C] [EnrichedCategory V D]

/-- Take the enriched opposite of an enriched functor. -/
def EnrichedFunctor.op (F : EnrichedFunctor V C D) :
    EnrichedFunctor V Cᵒᵖ Dᵒᵖ where
  obj X := Opposite.op (F.obj X.unop)
  map X Y := F.map Y.unop X.unop
  map_id X := F.map_id X.unop
  map_comp X Y Z := by
    change ((β_ (Y.unop ⟶[V] X.unop) (Z.unop ⟶[V] Y.unop)).hom ≫
          eComp V Z.unop Y.unop X.unop) ≫ F.map Z.unop X.unop =
      (F.map Y.unop X.unop ⊗ₘ F.map Z.unop Y.unop) ≫
        (β_ (F.obj Y.unop ⟶[V] F.obj X.unop)
          (F.obj Z.unop ⟶[V] F.obj Y.unop)).hom ≫
        eComp V (F.obj Z.unop) (F.obj Y.unop) (F.obj X.unop)
    rw [Category.assoc, F.map_comp]
    simpa only [Category.assoc] using
      (BraidedCategory.braiding_naturality_assoc
        (F.map Y.unop X.unop) (F.map Z.unop Y.unop)
        (eComp V (F.obj Z.unop) (F.obj Y.unop) (F.obj X.unop))).symm

end CategoryTheory
