# Contractible Tail Counterexample Formalization

This note sharpens the w76 obstruction into a smaller Lean-consumable contract for the concrete counterexample to bare boundedness transport along `HomotopyEquiv`.

The new audit file `audit/blockers/contractible_tail_counterexample_formalization.lean` proves the strict support part directly: if a cochain complex has nonzero terms arbitrarily far to the right, then it cannot satisfy `boundedCochainComplex`. This is the part of the contractible-tail example that should be independent of the eventual construction of infinite tails.

The file then packages the intended counterexample as `ContractibleTailCounterexampleData`: a bounded representative, a contractible tail, an unbounded selected model with explicit right-unbounded nonzero terms, and a `HomotopyEquiv` from the bounded representative to the selected model. From those fields it proves `not_strictBoundednessTransport_of_contractibleTailCounterexampleData`, so any future concrete instance immediately refutes the unsafe transport theorem.

The remaining missing API is isolated as `ContractibleTailAttachmentAPI`. It should attach an unbounded contractible tail to a bounded representative, preserve right-unbounded support in the selected model, and produce the homotopy equivalence back to the bounded representative. In mathlib terms this is where infinite direct-sum/product or shift-tail machinery would enter; it is not needed for the downstream refutation once `ContractibleTailCounterexampleData` is available.

For the target thread, the actionable point is unchanged but now more formal: strict `boundedCochainComplex` data may be transported by cochain isomorphism, not by arbitrary `HomotopyEquiv`, unless the theorem carries extra support-control hypotheses or selects a bounded representative separately.
