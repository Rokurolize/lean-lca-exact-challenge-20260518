import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientDifferentialExpansion

/-! # The corrected Drinfeld quotient Hom complex -/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory

def quotientDGMappingCochainComplex (X Y : ComplexCategory) :
    CochainComplex (ModuleCat.{1} ℤ) ℤ where
  X n := quotientGradedModule X Y n
  d n m := if h : n + 1 = m then
      quotientTotalDifferential X Y n ≫
        eqToHom (congrArg (quotientGradedModule X Y) h)
    else 0
  shape n m hnm := by
    change ¬n + 1 = m at hnm
    simp [hnm]
  d_comp_d' i j k hij hjk := by
    change i + 1 = j at hij
    change j + 1 = k at hjk
    subst j
    subst k
    simpa [Category.assoc] using quotientTotalDifferential_square X Y i

@[simp]
theorem quotientDGMappingCochainComplex_X
    (X Y : ComplexCategory) (n : ℤ) :
    (quotientDGMappingCochainComplex X Y).X n = quotientGradedModule X Y n :=
  rfl

@[simp]
theorem quotientDGMappingCochainComplex_d_succ
    (X Y : ComplexCategory) (n : ℤ) :
    (quotientDGMappingCochainComplex X Y).d n (n + 1) =
      quotientTotalDifferential X Y n := by
  simp [quotientDGMappingCochainComplex]

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
