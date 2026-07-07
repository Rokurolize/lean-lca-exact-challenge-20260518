# Next Steps: cycle-object exact acyclicity

Remote branch: `cycle-object-exact-acyclic-handoff-20260708`.

Implemented files:

- `LeanLCAExactChallenge/Derived/ExactAcyclicCorrect.lean`
- `audit/SCOPE.md`
- `audit/REPORT.md`

Verification command summary:

```bash
export PATH="$HOME/.elan/toolchains/leanprover--lean4---v4.30.0/bin:$PATH"
LIBS=$(find .lake -path '*/build/lib/lean' -type d | sort | paste -sd: -)
LDLIBS=$(find .lake -path '*/build/lib' -type d | sort | paste -sd: -)
export LEAN_PATH="$LIBS:$PWD"
export LD_LIBRARY_PATH="$LDLIBS"
lean -j1 -o .lake/build/lib/lean/LeanLCAExactChallenge/Derived/ExactAcyclicCorrect.olean \
  -i .lake/build/lib/lean/LeanLCAExactChallenge/Derived/ExactAcyclicCorrect.ilean \
  LeanLCAExactChallenge/Derived/ExactAcyclicCorrect.lean
lean -j1 LeanLCAExactChallenge.lean
```

Remaining tasks:

1. Prove shift closure for `exactAcyclicWithCycles`.
2. Prove mapping-cone isomorphism invariance.
3. Prove biproduct or finite-product closure as needed.
4. Build the `Dbounded` route using `boundedExactWeakEquivalenceWithCycles`.
5. Migrate legacy `exactAcyclic` lemmas theorem-by-theorem.

Note: this checkout had unrelated dirty files before this work began. This pass intentionally committed only the new cycle-object acyclicity artifacts and the one import line needed for them.
