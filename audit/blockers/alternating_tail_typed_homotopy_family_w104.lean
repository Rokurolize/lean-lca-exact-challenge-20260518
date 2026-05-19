import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.AlternatingConst
import Mathlib.Algebra.Homology.Homotopy

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open HomologicalComplex
open ComplexShape

namespace AlternatingTailTypedHomotopyFamilyW104

/-- The concrete additive category for the typed alternating-tail probe. -/
abbrev IntModuleCat := ModuleCat.{0} ℤ

/-- The constant object used in the alternating tail. -/
noncomputable abbrev moduleInt : IntModuleCat := ModuleCat.of ℤ ℤ

/-- The Nat-indexed alternating cochain complex with differentials `id, 0, id, 0, ...`. -/
noncomputable def natAlternatingTail : CochainComplex IntModuleCat ℕ :=
  HomologicalComplex.alternatingConst moduleInt
    (φ := 𝟙 moduleInt) (ψ := 0)
    (by simp) (by simp)
    (fun _ _ h => ComplexShape.up_nat_odd_add h)

/-- The homotopy component is active exactly from an odd source degree to its predecessor. -/
def parityOppositeActive (i j : ℕ) : Prop :=
  Odd i ∧ j + 1 = i

lemma parityOppositeActive_of_even_source_next {i : ℕ} (hi : Even i) :
    parityOppositeActive (i + 1) i := by
  rcases hi with ⟨k, rfl⟩
  exact ⟨⟨k, by omega⟩, by omega⟩

lemma parityOppositeActive_of_odd_source_prev {i : ℕ} (hi : Odd i) :
    parityOppositeActive i (i - 1) := by
  rcases hi with ⟨k, rfl⟩
  constructor
  · exact ⟨k, rfl⟩
  · omega

lemma not_parityOppositeActive_of_self {i : ℕ} :
    ¬ parityOppositeActive i i := by
  rintro ⟨_, h⟩
  omega

lemma not_parityOppositeActive_zero_target {i : ℕ} (hi : Even i) :
    ¬ parityOppositeActive i (i - 1) := by
  intro h
  exact Nat.not_odd_iff_even.mpr hi h.1

/-- The typed candidate `s i j : K.X i ⟶ K.X j`.

The branch condition follows w102: use the identity on the odd-source predecessor branch and
zero elsewhere. Because `natAlternatingTail.X n` is definitionally `moduleInt`, the identity
branch is a genuine typed morphism family rather than an untyped arithmetic marker. -/
noncomputable def natAlternatingTailHom (i j : ℕ) :
    (natAlternatingTail).X i ⟶ (natAlternatingTail).X j :=
  by
    classical
    exact if h : parityOppositeActive i j then 𝟙 moduleInt else 0

lemma natAlternatingTailHom_active {i j : ℕ} (h : parityOppositeActive i j) :
    natAlternatingTailHom i j = 𝟙 moduleInt := by
  simp [natAlternatingTailHom, h]

lemma natAlternatingTailHom_inactive {i j : ℕ} (h : ¬ parityOppositeActive i j) :
    natAlternatingTailHom i j = 0 := by
  simp [natAlternatingTailHom, h]

lemma natAlternatingTailHom_zero_self (i : ℕ) :
    natAlternatingTailHom i i = 0 :=
  natAlternatingTailHom_inactive not_parityOppositeActive_of_self

lemma natAlternatingTailHom_zero_prev_of_even {i : ℕ} (hi : Even i) :
    natAlternatingTailHom i (i - 1) = 0 :=
  natAlternatingTailHom_inactive (not_parityOppositeActive_zero_target hi)

lemma natAlternatingTail_d_even {i j : ℕ}
    (hij : (ComplexShape.up ℕ).Rel i j) (hi : Even i) :
    natAlternatingTail.d i j = 𝟙 moduleInt := by
  have hij' : i + 1 = j := hij
  simp [natAlternatingTail, HomologicalComplex.alternatingConst, hij', hi]

lemma natAlternatingTail_d_odd {i j : ℕ}
    (hij : (ComplexShape.up ℕ).Rel i j) (hi : Odd i) :
    natAlternatingTail.d i j = 0 := by
  have hij' : i + 1 = j := hij
  have hne : ¬ Even i := Nat.not_even_iff_odd.mpr hi
  simp [natAlternatingTail, HomologicalComplex.alternatingConst, hij', hne]
  rfl

lemma even_pred_of_odd {i : ℕ} (hi : Odd i) : Even (i - 1) := by
  rcases hi with ⟨k, rfl⟩
  exact ⟨k, by omega⟩

/-- Even target degrees get the identity contribution from the `dNext` summand. -/
lemma dNext_even_eq_id {i : ℕ} (hi : Even i) :
    dNext i natAlternatingTailHom = 𝟙 ((natAlternatingTail).X i) := by
  rw [dNext_eq natAlternatingTailHom (show (ComplexShape.up ℕ).Rel i (i + 1) by rfl)]
  rw [natAlternatingTail_d_even (show (ComplexShape.up ℕ).Rel i (i + 1) by rfl) hi]
  rw [natAlternatingTailHom_active (parityOppositeActive_of_even_source_next hi)]
  simp [natAlternatingTail]

/-- Even target degrees get no contribution from the `prevD` summand. -/
lemma prevD_even_eq_zero {i : ℕ} (hi : Even i) :
    prevD i natAlternatingTailHom = 0 := by
  rw [prevD_nat natAlternatingTail natAlternatingTail i natAlternatingTailHom]
  rw [natAlternatingTailHom_zero_prev_of_even hi]
  simp

/-- The exact full equation left for the odd branch and later `ℤ`-tail transport. -/
abbrev ContractingHomotopyEquations
    (s : ∀ i j : ℕ, (natAlternatingTail).X i ⟶ (natAlternatingTail).X j) : Prop :=
  ∀ i : ℕ, (𝟙 natAlternatingTail : natAlternatingTail ⟶ natAlternatingTail).f i =
    dNext i s + prevD i s + (0 : natAlternatingTail ⟶ natAlternatingTail).f i

lemma dNext_odd_eq_zero {i : ℕ} (hi : Odd i) :
    dNext i natAlternatingTailHom = 0 := by
  rw [dNext_eq natAlternatingTailHom (show (ComplexShape.up ℕ).Rel i (i + 1) by rfl)]
  rw [natAlternatingTail_d_odd (show (ComplexShape.up ℕ).Rel i (i + 1) by rfl) hi]
  simp

lemma prevD_odd_eq_id {i : ℕ} (hi : Odd i) :
    prevD i natAlternatingTailHom = 𝟙 ((natAlternatingTail).X i) := by
  rw [prevD_nat natAlternatingTail natAlternatingTail i natAlternatingTailHom]
  rw [natAlternatingTailHom_active (parityOppositeActive_of_odd_source_prev hi)]
  rw [natAlternatingTail_d_even (show (ComplexShape.up ℕ).Rel (i - 1) i by
    rcases hi with ⟨k, rfl⟩
    simp) (even_pred_of_odd hi)]
  simp [natAlternatingTail]

/-- The focused even-degree segment of the `Homotopy.comm` contracting-homotopy equation. -/
lemma contractingHomotopyEquation_even_segment {i : ℕ} (hi : Even i) :
    (𝟙 natAlternatingTail : natAlternatingTail ⟶ natAlternatingTail).f i =
      dNext i natAlternatingTailHom + prevD i natAlternatingTailHom +
        (0 : natAlternatingTail ⟶ natAlternatingTail).f i := by
  rw [dNext_even_eq_id hi, prevD_even_eq_zero hi]
  simp

/-- Odd target degrees get the identity contribution from the `prevD` summand. -/
lemma contractingHomotopyEquation_odd_segment {i : ℕ} (hi : Odd i) :
    (𝟙 natAlternatingTail : natAlternatingTail ⟶ natAlternatingTail).f i =
      dNext i natAlternatingTailHom + prevD i natAlternatingTailHom +
        (0 : natAlternatingTail ⟶ natAlternatingTail).f i := by
  rw [dNext_odd_eq_zero hi, prevD_odd_eq_id hi]
  simp

/-- The Nat-indexed alternating tail has a contracting homotopy from the identity to zero. -/
theorem natAlternatingTail_contractingHomotopyEquations :
    ContractingHomotopyEquations natAlternatingTailHom := by
  intro i
  rcases i.even_or_odd with hi | hi
  · exact contractingHomotopyEquation_even_segment hi
  · exact contractingHomotopyEquation_odd_segment hi

/-- The Nat-indexed alternating tail is contractible. -/
noncomputable def natAlternatingTailContractingHomotopy :
    Homotopy (𝟙 natAlternatingTail) (0 : natAlternatingTail ⟶ natAlternatingTail) where
  hom := natAlternatingTailHom
  zero := by
    intro i j hrel
    exact natAlternatingTailHom_inactive (by
      rintro ⟨_, hij⟩
      exact hrel hij)
  comm := natAlternatingTail_contractingHomotopyEquations

#check natAlternatingTailHom
#check natAlternatingTailHom_active
#check dNext_even_eq_id
#check prevD_even_eq_zero
#check contractingHomotopyEquation_even_segment
#check dNext_odd_eq_zero
#check prevD_odd_eq_id
#check contractingHomotopyEquation_odd_segment
#check natAlternatingTail_contractingHomotopyEquations
#check natAlternatingTailContractingHomotopy
#check ContractingHomotopyEquations
#check Homotopy.comm
#check dNext_eq
#check prevD_nat

end AlternatingTailTypedHomotopyFamilyW104

end LeanLCAExactChallenge
