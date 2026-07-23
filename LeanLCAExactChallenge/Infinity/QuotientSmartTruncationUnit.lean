import LeanLCAExactChallenge.Infinity.QuotientSmartTruncationMonoidal

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section
attribute [-instance] ULift.semiring

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord
namespace QuotientSmartTruncation

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

abbrev CUnit : QuotientDGCochain := 𝟙_ QuotientDGCochain
abbrev ChUnit : QuotientDoldKanMonoidal.QuotientChain :=
  𝟙_ QuotientDoldKanMonoidal.QuotientChain

private lemma cochainUnitSpan_d :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (𝟙_ QuotientDoldKanMonoidal.QuotientModule)).inv ≫
      CUnit.d 0 1 = 0 := by
  change ((HomologicalComplex.single
    QuotientDoldKanMonoidal.QuotientModule (ComplexShape.up ℤ) 0).obj
      (𝟙_ QuotientDoldKanMonoidal.QuotientModule)).d 0 1 = 0
  rw [HomologicalComplex.single_obj_d]

/-- The monoidal unit in smart-truncation degree zero. -/
def unitDegreeZero :
    𝟙_ QuotientDoldKanMonoidal.QuotientModule ⟶
      (functor.obj CUnit).X 0 := by
  have hb : ComplexShape.embeddingDownNat.BoundaryLE 0 := by
    simpa [ComplexShape.embeddingDownNat, ComplexShape.embeddingUpIntLE] using
      (ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).2 rfl
  exact
    CUnit.liftCycles'
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ QuotientDoldKanMonoidal.QuotientModule)).inv
        1 rfl cochainUnitSpan_d ≫
      (CUnit.truncLE'XIsoCycles
        ComplexShape.embeddingDownNat rfl hb).inv


lemma unitDegreeZero_toRestriction :
    unitDegreeZero ≫
        (CUnit.truncLE'ToRestriction ComplexShape.embeddingDownNat).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ QuotientDoldKanMonoidal.QuotientModule)).inv := by
  have hb : ComplexShape.embeddingDownNat.BoundaryLE 0 := by
    simpa [ComplexShape.embeddingDownNat, ComplexShape.embeddingUpIntLE] using
      (ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).2 rfl
  rw [quotientTruncLEToRestriction_f_zero _ hb]
  dsimp [unitDegreeZero]
  simp only [Category.assoc]
  erw [quotientTruncLEIsoCycles_inv_hom_of_proofs_assoc
    CUnit 0 0 rfl rfl hb hb]
  simp

/-- The monoidal unit comparison for smart truncation. -/
def unit : ChUnit ⟶ functor.obj CUnit :=
  (ChainComplex.fromSingle₀Equiv
    (functor.obj CUnit)
    (𝟙_ QuotientDoldKanMonoidal.QuotientModule)).symm unitDegreeZero

@[simp]
lemma unit_f_zero : unit.f 0 = unitDegreeZero := by
  exact ChainComplex.fromSingle₀Equiv_symm_apply_f_zero unitDegreeZero

end QuotientSmartTruncation
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
