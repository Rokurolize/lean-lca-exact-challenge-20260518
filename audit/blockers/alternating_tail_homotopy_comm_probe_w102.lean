import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.AlternatingConst
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Homotopy

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open ComplexShape

namespace AlternatingTailHomotopyCommProbeW102

/-- The concrete additive category for the alternating-tail probe. -/
abbrev IntModuleCat := ModuleCat.{0} ℤ

/-- The constant object used in the alternating tail. -/
noncomputable abbrev moduleInt : IntModuleCat := ModuleCat.of ℤ ℤ

/-- The `ℕ`-indexed alternating cochain complex
`0 ⟶ ℤ --𝟙--> ℤ --0--> ℤ --𝟙--> ℤ --0--> ...`. -/
noncomputable def natAlternatingTail : CochainComplex IntModuleCat ℕ :=
  HomologicalComplex.alternatingConst moduleInt
    (φ := 𝟙 moduleInt) (ψ := 0)
    (by simp) (by simp)
    (fun _ _ h => ComplexShape.up_nat_odd_add h)

/-- The corresponding `ℤ`-indexed tail, zero below `p` and alternating in every degree
`p + n`. -/
noncomputable def intAlternatingTailGE (p : ℤ) : CochainComplex IntModuleCat ℤ :=
  natAlternatingTail.extend (ComplexShape.embeddingUpIntGE p)

/-- The homotopy-component shape suggested by the alternating tail: a component is active
exactly from an odd source degree to its predecessor. On the actual complex this is the
parity-opposite candidate for the `s i j` family in `Homotopy.comm`. -/
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

lemma not_parityOppositeActive_of_even_source {i j : ℕ} (hi : Even i) :
    ¬ parityOppositeActive i j := by
  intro h
  exact Nat.not_odd_iff_even.mpr hi h.1

/-- A local arithmetic model of the two summands in the `Homotopy.comm` equation.

For even `i`, `dNext i s` is the active summand; for odd `i`, `prevD i s` is active. -/
lemma homotopyComm_parity_local (i : ℕ) :
    parityOppositeActive (i + 1) i ∨ parityOppositeActive i (i - 1) := by
  rcases i.even_or_odd with hi | hi
  · exact Or.inl (parityOppositeActive_of_even_source_next hi)
  · exact Or.inr (parityOppositeActive_of_odd_source_prev hi)

/-- The exact mathlib `Homotopy.comm` equation to prove for a contracting homotopy from
`𝟙` to `0`. -/
abbrev ContractingHomotopyEquations (K : CochainComplex IntModuleCat ℕ)
    (s : ∀ i j : ℕ, K.X i ⟶ K.X j) : Prop :=
  ∀ i : ℕ, (𝟙 K : K ⟶ K).f i = dNext i s + prevD i s + (0 : K ⟶ K).f i

/-- The `ℤ`-indexed target still needs the same data after transport along
`embeddingUpIntGE`. -/
abbrev IntTailContractingHomotopyData (p : ℤ) : Type :=
  { s : ∀ i j : ℤ, (intAlternatingTailGE p).X i ⟶ (intAlternatingTailGE p).X j //
    (∀ i j : ℤ, ¬ (ComplexShape.up ℤ).Rel j i → s i j = 0) ∧
      ∀ i : ℤ, (𝟙 (intAlternatingTailGE p) : intAlternatingTailGE p ⟶
          intAlternatingTailGE p).f i =
        dNext i s + prevD i s + (0 : intAlternatingTailGE p ⟶ intAlternatingTailGE p).f i }

#check Homotopy
#check Homotopy.hom
#check Homotopy.zero
#check Homotopy.comm
#check dNext
#check dNext_eq
#check prevD
#check prevD_eq
#check HomologicalComplex.alternatingConst
#check ComplexShape.embeddingUpIntGE
#check HomologicalComplex.extend
#check HomologicalComplex.extendXIso
#check natAlternatingTail
#check intAlternatingTailGE
#check parityOppositeActive
#check homotopyComm_parity_local
#check ContractingHomotopyEquations
#check IntTailContractingHomotopyData

end AlternatingTailHomotopyCommProbeW102

end LeanLCAExactChallenge
