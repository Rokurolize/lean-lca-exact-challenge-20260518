import Mathlib.CategoryTheory.Adjunction.Basic

/-!
W250 audit: generic unit/counit equalities for adjunction transport.

Mathlib transports adjunctions across natural isomorphisms by
`Adjunction.ofNatIsoLeft` and `Adjunction.ofNatIsoRight`. This file packages
the unit and counit equations needed by the localized-comparison frontier.
-/

set_option autoImplicit false

noncomputable section

universe v₁ v₂ u₁ u₂

namespace LeanLCAExactChallenge

open CategoryTheory

namespace AdjunctionTransportUnitEqualityW250

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- Transport an adjunction across a natural isomorphism of its left adjoint. -/
def transportOfNatIsoLeft {F F' : C ⥤ D} {R : D ⥤ C}
    (adj : F ⊣ R) (e : F ≅ F') : F' ⊣ R :=
  adj.ofNatIsoLeft e

/-- Unit equation for left-adjoint transport. -/
theorem transportOfNatIsoLeft_unit {F F' : C ⥤ D} {R : D ⥤ C}
    (adj : F ⊣ R) (e : F ≅ F') :
    (transportOfNatIsoLeft adj e).unit =
      adj.unit ≫ (Functor.isoWhiskerRight e R).hom := by
  simp [transportOfNatIsoLeft, Adjunction.ofNatIsoLeft, Functor.isoWhiskerRight_hom]

/-- Transport an adjunction across a natural isomorphism of its right adjoint. -/
def transportOfNatIsoRight {L : C ⥤ D} {F F' : D ⥤ C}
    (adj : L ⊣ F) (e : F ≅ F') : L ⊣ F' :=
  adj.ofNatIsoRight e

/-- Counit equation for right-adjoint transport, with the corrected orientation. -/
theorem transportOfNatIsoRight_counit {L : C ⥤ D} {F F' : D ⥤ C}
    (adj : L ⊣ F) (e : F ≅ F') :
    (transportOfNatIsoRight adj e).counit =
      (Functor.isoWhiskerRight e L).symm.hom ≫ adj.counit := by
  simp [transportOfNatIsoRight, Adjunction.ofNatIsoRight, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerRight_symm]

def adjunctionTransportUnitEqualityFindings : List String :=
  ["Adjunction.ofNatIsoLeft transports F ⊣ R along e : F ≅ F'",
    "Adjunction.ofNatIsoRight transports L ⊣ F along e : F ≅ F'",
    "left-adjoint transport unit is adj.unit ≫ (Functor.isoWhiskerRight e R).hom",
    "right-adjoint transport counit is (Functor.isoWhiskerRight e L).symm.hom ≫ adj.counit",
    "these are generic inputs for localized-comparison membership transport",
    "this audit does not construct the concrete localized comparison adjunction"]

theorem adjunctionTransportUnitEqualityFindings_count :
    adjunctionTransportUnitEqualityFindings.length = 6 := rfl

section Checks

#check Adjunction.ofNatIsoLeft
#check Adjunction.ofNatIsoRight
#check transportOfNatIsoLeft
#check transportOfNatIsoLeft_unit
#check transportOfNatIsoRight
#check transportOfNatIsoRight_counit
#check adjunctionTransportUnitEqualityFindings_count

end Checks

end AdjunctionTransportUnitEqualityW250

end LeanLCAExactChallenge
