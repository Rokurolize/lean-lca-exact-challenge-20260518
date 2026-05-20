# Alternating Tail Typed Homotopy Family W104

Worker `w104-alternating-tail-typed-homotopy-family` followed the w95/w102 route and narrowed the next proof step to the Nat-indexed typed morphism family for mathlib's `Homotopy.comm` equation.

The compiling audit file `audit/blockers/alternating_tail_typed_homotopy_family_w104.lean` defines:

- `natAlternatingTail`, the `CochainComplex (ModuleCat ℤ) ℕ` built with `HomologicalComplex.alternatingConst moduleInt (φ := 𝟙 moduleInt) (ψ := 0)`;
- `parityOppositeActive i j := Odd i ∧ j + 1 = i`, matching w102's active branch;
- `natAlternatingTailHom i j : natAlternatingTail.X i ⟶ natAlternatingTail.X j`, using the identity on the active branch and zero otherwise;
- `contractingHomotopyEquation_even_segment`, proving the even target-degree part of `(𝟙 natAlternatingTail).f i = dNext i s + prevD i s + (0 : natAlternatingTail ⟶ natAlternatingTail).f i`.

The even proof splits exactly as expected: `dNext i natAlternatingTailHom = 𝟙` for even `i`, while `prevD i natAlternatingTailHom = 0`. This gives a typed proof segment rather than only a parity arithmetic note.

The remaining obstruction is now precise. The odd target-degree segment should prove the dual split, with `dNext i natAlternatingTailHom = 0` and `prevD i natAlternatingTailHom = 𝟙` for odd `i`. After that Nat-indexed `ContractingHomotopyEquations` proof exists, the `ℤ`-indexed tail still needs transport through `ComplexShape.embeddingUpIntGE` and `HomologicalComplex.extendXIso`, where heterogeneous object equalities are the likely `eqToHom`/cast pressure point.


Parent extension at 2026-05-19T22:40:00Z: after porting W104, the parent proved the odd target-degree dual and assembled `natAlternatingTail_contractingHomotopyEquations`. It also constructed `natAlternatingTailContractingHomotopy : Homotopy (𝟙 natAlternatingTail) 0`. The remaining obstruction is now specifically the transport from this Nat-indexed contractible complex to the `ℤ`-indexed `intAlternatingTailGE p`, and then connecting that transported complex to `UnboundedContractibleTailInstance`.
