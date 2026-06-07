import LeanLCAExactChallenge.LCA.ExactCategory

set_option autoImplicit false

universe u

namespace LeanLCAExactChallenge

open CategoryTheory

namespace MetrizableLCA

example {X Y Z : MetrizableLCA.{u}} {i : X ⟶ Y} {j : Y ⟶ Z}
    (hi : QuillenExactCategory.inflation i) (hj : QuillenExactCategory.inflation j) :
    QuillenExactCategory.inflation (i ≫ j) := by
  rw [quillenInflation_iff_exists_strictShortExact] at hi hj ⊢
  rcases hi with ⟨Zi, gi, zi, hSi⟩
  rcases hj with ⟨Zj, gj, zj, hSj⟩
  exact ?inflation_comp_missing

example {X Y Z : MetrizableLCA.{u}} {p : X ⟶ Y} {q : Y ⟶ Z}
    (hp : QuillenExactCategory.deflation p) (hq : QuillenExactCategory.deflation q) :
    QuillenExactCategory.deflation (p ≫ q) := by
  rw [quillenDeflation_iff_exists_strictShortExact] at hp hq ⊢
  rcases hp with ⟨Wp, fp, zp, hSp⟩
  rcases hq with ⟨Wq, fq, zq, hSq⟩
  exact ?deflation_comp_missing

end MetrizableLCA

end LeanLCAExactChallenge
