# Handover: completing the corrected bounded derived category for MetrizableLCA

Audience: the engineer (human or agent) who continues this work with **zero session
context**. Everything you need is in this file, the repo, and the audit files it points
to. Read it top to bottom once before touching anything. I am retiring from this
task today; you are not inheriting my context window, so I have written down the parts
that were only in my head — especially the *decisions* and the *reasons*, because the
code alone does not explain why certain obvious-looking approaches are forbidden.

---

## 0. TL;DR

- Parts 1–3 of the challenge (Quillen exact categories; MetrizableLCA as an exact
  category; Yoneda Ext) are **done and verified**. Do not reopen them.
- Part 4 (bounded derived category `D^b`) has a **corrected route** built on
  `exactAcyclicWithCycles` / `boundedExactWeakEquivalenceWithCycles`. Your job is to
  make `DboundedWithCycles MetrizableLCA.{0}` carry its stable package **by proof**,
  eliminating the explicit assumption surface in
  `LeanLCAExactChallenge/BoundedDerived/MetrizableStableBridgeWithCycles.lean`.
- The architecture is frozen (§4): mirror mathlib's `DerivedCategory` Q/Qh pattern.
  Do **not** try to prove chain-level calculus of fractions (§4.2 explains why it is
  believed false). Do **not** try to prove `HasFiniteLimits`/`HasFiniteColimits` on the
  ordinary localization (§4.3 explains why it is believed false).
- Work through the milestone ladder in §6, one theorem per iteration:
  compile → audit update → commit → fast-forward push.
- Non-negotiables in §2. Review checklist you must run after every change in §8.
- If you get stuck: blocker report per §10, never a success claim.

## 1. The mission

Original four-part task:

1. Formalize Quillen exact categories in Lean. — **done** (`ExactCategory/Basic.lean`).
2. Prove MetrizableLCA (conflations = closed inclusions / open surjections with the
   underlying abelian-group kernel/cokernel condition) is an exact category. — **done**
   (`LCA/ExactCategory.lean`).
3. Formalize Yoneda-Ext groups using that exact structure. — **done** (`Ext/Yoneda.lean`).
4. Formalize the bounded derived (∞-)category `D^b(C,E)`. — **the remaining work.**

History you must know: an earlier attempt used a **degreewise** acyclicity predicate
`exactAcyclic` ("every `K.sc i` is a conflation"). That definition is mathematically
wrong (too strong; not the exact-category notion of acyclic). It was replaced by the
corrected cycle-object predicate. The legacy predicate and everything downstream of it
(`boundedExactWeakEquivalence`, `Dbounded`, the legacy stable bridge) remain in the
repo **as compatibility artifacts only**. The single most important rule of this task:

> **The corrected route must never use the legacy degreewise predicate as mathematical
> justification.** Legacy declarations may be *mirrored* (same architectural shape) but
> never *consumed* (as proof ingredients for corrected statements).

### Definition of done

All of the following, simultaneously:

- The corrected route uses `exactAcyclicWithCycles` and
  `boundedExactWeakEquivalenceWithCycles` as its mathematical content.
- `DboundedWithCycles MetrizableLCA.{0}` has the stable package fields **by proof**,
  with no unresolved assumption surface for: calculus of fractions, pretriangulated,
  triangulated — and the finite-limit/finite-colimit fields resolved per §4.3 (honest
  replacement + written impossibility rationale, since they are believed unprovable).
- `currentMetrizableStableBridgeWithCyclesProductSuccessClaimed` stops being `false`
  **only when** the corrected stable package is genuinely inhabited (§9).
- No `sorry`, `admit`, new `axiom`, or `unsafe` anywhere in touched files.
- Every touched Lean file and `LeanLCAExactChallenge.lean` pass direct `lean -j1`.
- `audit/REPORT.md` states exactly what was proved, what legacy artifacts remain, and
  why the corrected route is complete.
- Final commit fast-forward pushed to `origin/main`.

If any of this cannot be achieved from the current foundations, done = a mathematically
precise blocker report (§10) instead.

## 2. Non-negotiable constraints

- No `sorry`, `admit`, new `axiom`, `unsafe`, `native_decide`.
- No legacy `exactAcyclic` / `boundedExactWeakEquivalence` / `Dbounded` as proof
  ingredients for corrected statements. Compatibility-only.
- Never force-push. Push only fast-forward to `origin/main` (§7).
- Never reset, clean, delete, or modify the sibling checkout
  `/home/roku/src/Rokurolize/lean-lca-exact-challenge-20260518`. It has unrelated
  dirty state and hosts the shared `.lake` build cache we symlink to.
- Do not "complete" the task by making a conditional assumption surface type-check.
  Type-checking an assumption is not proving it.
- Do not migrate the Lean/mathlib toolchain as part of this task. The repo is
  coherently pinned (`leanprover/lean4:v4.30.0`, mathlib rev
  `c5ea00351c28e24afc9f0f84379aa41082b1188f`, matching compiled cache). A `v4.31.0`
  migration is a separate task with its own protocol (see `audit/REPORT.md`,
  "Version policy"). Changing `lean-toolchain` alone creates an incoherent
  verification state.

## 3. Workspace, environment, verification

Repo (work here): `/home/roku/src/Rokurolize/lean-lca-exact-challenge-20260518-origin-main-push-20260708`
Branch: `integrate-cycle-object-main-20260708`; it tracks and pushes to `origin/main`.

Start-of-session ritual (always recompute live state; never trust stale hashes):

```bash
cd /home/roku/src/Rokurolize/lean-lca-exact-challenge-20260518-origin-main-push-20260708
git status --short --branch
git log --oneline --decorate -12
git fetch origin main
git log --oneline --decorate --left-right --cherry-pick --boundary HEAD...origin/main | head -80
```

Lean environment (no `lake build` here; we drive `lean` directly against the shared
compiled cache):

```bash
export PATH="$HOME/.elan/toolchains/leanprover--lean4---v4.30.0/bin:$PATH"
if [ ! -e .lake ]; then ln -s /home/roku/src/Rokurolize/lean-lca-exact-challenge-20260518/.lake .lake; fi
LIBS=$(find -L .lake -path '*/build/lib/lean' -type d | sort | paste -sd: -)
LDLIBS=$(find -L .lake -path '*/build/lib' -type d | sort | paste -sd: -)
export LEAN_PATH="$LIBS:$PWD"
export LD_LIBRARY_PATH="$LDLIBS"
```

Baseline verification (all must exit 0):

```bash
lean -j1 LeanLCAExactChallenge/ExactCategory/Basic.lean
lean -j1 LeanLCAExactChallenge/LCA/ExactCategory.lean
lean -j1 LeanLCAExactChallenge/Ext/Yoneda.lean
lean -j1 LeanLCAExactChallenge/Derived/ExactAcyclicCorrect.lean
lean -j1 LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesClosure.lean
lean -j1 LeanLCAExactChallenge/Derived/BoundedDerivedWithCycles.lean
lean -j1 LeanLCAExactChallenge/BoundedDerived/MetrizableStableBridgeWithCycles.lean
lean -j1 LeanLCAExactChallenge.lean
```

**Trap — the root-module check:** `lean -j1 LeanLCAExactChallenge.lean` resolves
imports via `LEAN_PATH`, i.e. via compiled `.olean`s. When you add a NEW module and its
import to `LeanLCAExactChallenge.lean`, you must first precompile the new module's
`.olean` into the cache, e.g.:

```bash
lean -j1 -o .lake/build/lib/lean/LeanLCAExactChallenge/Foo/Bar.olean \
  -i .lake/build/lib/lean/LeanLCAExactChallenge/Foo/Bar.ilean \
  LeanLCAExactChallenge/Foo/Bar.lean
```

then run the root check. (This writes into the shared cache under the sibling checkout;
that is its purpose — but never delete or rebuild that cache wholesale.)
Similarly, when you EDIT an existing module, downstream checks read the stale `.olean`
until you recompile it the same way. Always recompile edited modules' oleans before
verifying their dependents, or your "verification" verifies yesterday's code.

## 4. The architecture (frozen — do not relitigate without new evidence)

### 4.1 What exists (corrected route)

- `Derived/ExactAcyclicCorrect.lean` —
  `ExactAcyclicWithCyclesData` (cycle objects `Z i`, conflations
  `Z i ⟶ K.X i ⟶ Z (i+1)`, differential factorization `proj ≫ incl = d`);
  `exactAcyclicWithCycles := Nonempty (…Data)`;
  `boundedExactWeakEquivalenceWithCycles C f :=
    exactAcyclicWithCycles C (mappingCone ((BoundedComplexCategory.ι C).map f))`
  (a `MorphismProperty (BoundedComplexCategory C)` — cone-acyclicity at chain level);
  MetrizableLCA specializations incl. `exactAcyclicWithCycles_iff_challengeCycleExactSequences`.
- `Derived/ExactAcyclicWithCyclesClosure.lean` — iso invariance, shift closure +
  `IsCompatibleWithShift ℤ`, zero, MetrizableLCA binary-biproduct and finite-product
  closure, `isStableUnderFiniteProducts_metrizableLCA`, mapping-cone congruence.
- `Derived/BoundedDerivedWithCycles.lean` —
  `DboundedWithCycles C := (boundedExactWeakEquivalenceWithCycles C).Localization`
  (localization of the **chain-level** bounded complex category), localization functor
  `:= W.Q`, plus conditional structure lemmas that consume a chain-level
  `HasLeftCalculusOfFractions` hypothesis.
- `BoundedDerived/MetrizableStableBridgeWithCycles.lean` — the assumption surface:
  `StablePackage` (preadditive, finite products, finite limits, finite colimits, zero
  object, shift-additivity, pretriangulated, triangulated),
  `LeftCalculusAssumption`, `LeftCalculusSemanticFields`,
  `RemainingStableSemanticFields`, constructors, and the honest success marker
  `currentMetrizableStableBridgeWithCyclesProductSuccessClaimed = false`.
- `LCA/IdempotentComplete.lean` (commit `0483f25f`) —
  `instance : IsIdempotentComplete MetrizableLCA.{u}` via mathlib's
  `isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent` + the project's
  `HasFiniteLimits MetrizableLCA` (from `LCA/Pullback.lean:160`). Milestone 1, done.

Base-category facts you may rely on: `MetrizableLCA` is preadditive, has binary
biproducts, **has all finite limits** (`LCA/Pullback.lean`), and is idempotent complete.
(Finite limits in the BASE category are fine; it is the derived category where they fail.)

### 4.2 Decision: mirror mathlib's DerivedCategory Q/Qh pattern

**Do not attempt to prove `(boundedExactWeakEquivalenceWithCycles C).HasLeftCalculusOfFractions`
at the chain level.** Reason: for cone-acyclicity classes on a category of complexes,
the left Ore condition is classically false — the candidate Ore square built from the
homotopy pushout `W = cone((-f, s) : X → Z ⊕ Y)` commutes only **up to homotopy**
(the discrepancy is exactly `dH + Hd` for `H : x ↦ (x,0,0)`), and there is no general
strictification. Calculus of fractions lives one floor up, in the homotopy category.
The legacy route, to its credit, never claimed chain-level calculus unconditionally
either (its `boundedExactWeakEquivalence_hasLeftCalculusOfFractions_of_isoClosed`,
`Derived/Bounded.lean:2385`, consumes a homotopy-level calculus hypothesis).

The honest plan, exactly like mathlib's `DerivedCategory` (`Q` vs `Qh`):

1. Present the corrected acyclics as a triangulated `ObjectProperty` `P` of the bounded
   homotopy category.
2. Mathlib then gives `P.trW.HasLeftCalculusOfFractions`, `HasRightCalculusOfFractions`,
   `IsCompatibleWithTriangulation` for free
   (`Mathlib/CategoryTheory/Triangulated/Subcategory.lean:588,607,626` in the pin;
   note this pin calls it `ObjectProperty.trW` — there is **no** `Subcategory.W`).
3. Show the chain-level localization `DboundedWithCycles C` is **also** a localization
   of the bounded homotopy category at `P.trW`: the chain localization functor inverts
   homotopy equivalences (needs milestones 2–3), hence factors through the homotopy
   quotient; `Functor.IsLocalization.of_comp`
   (`Mathlib/CategoryTheory/Localization/Composition.lean:114`) upgrades the factored
   functor `Lh : K^b → DboundedWithCycles C` to `Lh.IsLocalization P.trW`.
4. Apply mathlib's generic localization theorems to `Lh` — they are stated for an
   arbitrary localization functor `L : C ⥤ D`, not just `W.Q`:
   `Localization.preadditive` (`Localization/CalculusOfFractions/Preadditive.lean:308`),
   `Triangulated.Localization.pretriangulated` (`Localization/Triangulated.lean:195`),
   `Triangulated.Localization.isTriangulated` (`:214`).
   These need `Lh.CommShift ℤ`; get it from the factorization and
   `commShiftOfLocalization` (`Mathlib/CategoryTheory/Shift/Localization.lean:176`).
   The shift on `DboundedWithCycles` already exists via
   `boundedExactWeakEquivalenceWithCycles_isCompatibleWithShift`
   (`ExactAcyclicWithCyclesClosure.lean:83`) + `HasShift.localization`
   (`Shift/Localization.lean:99`).

Net effect: the chain-level calculus assumption **dissolves** — nothing in the final
package needs it. `LeftCalculusAssumption` in the bridge becomes a legacy-shaped
compatibility artifact; the package gets built through a new, honest constructor.

### 4.3 Decision: finite limits/colimits on the ordinary category are not to be proved

`HasFiniteLimits (DboundedWithCycles MetrizableLCA.{0})` and its colimit twin are
believed **false**: a triangulated category has weak (co)kernels via cones, not
equalizers/kernels; possessing all finite limits would force a semisimple-like
collapse, and `MetrizableLCA` is not split-semisimple (the conflation
`ℤ ↪ ℝ ↠ 𝕋` does not split: every continuous homomorphism `ℝ → ℤ` is zero, so no
retraction exists). Finite limits/colimits are features of the stable ∞-category, not
of its ordinary homotopy category. Independently confirmed by a second-model review
(GPT-5.5 Pro, 2026-07-08) and consistent with Bühler.

Resolution when you reach §6 milestone 9: build an honest replacement package
(preadditive, zero object, finite products **and finite coproducts** (or biproducts),
shift-additivity, pretriangulated, triangulated), keep the two unprovable fields out of
the success-bearing structure, and write the impossibility rationale into
`audit/REPORT.md`. Do not sink proof effort into inhabiting them; do not fake them.
We do not currently plan to *formalize* the falsity (that would need
"triangulated + finite limits ⇒ semisimple" in Lean — out of scope); a precise prose
rationale in the audit is the agreed standard.

### 4.4 Where idempotent completeness enters (calibrated by Bühler ch. 10)

- Cone of a map between acyclics (Lemma 10.3): needs **no** idempotent completeness.
- Contractible ⇒ acyclic (Prop. 10.9-style): needs idempotent splitting — we have full
  `IsIdempotentComplete MetrizableLCA` (stronger than the weak completeness Bühler
  needs), so cite the instance and move on.
- Thickness of `Ac^b` in `K^b` (closure under direct summands), and
  "iso in `D^b` iff cone acyclic": weak idempotent completeness — again covered.

## 5. The legacy skeleton you should mirror (but never consume)

All in `Derived/Bounded.lean` (line numbers as of commit `0483f25f`):

- `exactAcyclicHomotopyObject : ObjectProperty (HomotopyCategory C (ComplexShape.up ℤ))`
  `:= fun K => exactAcyclic C K.as` (line 426) — the pattern for lifting a chain-level
  predicate to the homotopy category; quotient-obj bridge is `Iff.rfl` (line 432).
- `exactAcyclicHomotopyIsoClosure := (…HomotopyObject C).isoClosure` (line 665) and
  `…IsoClosure_trW = …Object.trW` via `ObjectProperty.trW_isoClosure` (line 710).
- `BoundedComplexCategory C := (boundedCochainComplex C).FullSubcategory` (line 190);
  `homotopyQuotient := ι ⋙ HomotopyCategory.quotient` (line 1114);
  `boundedHomotopyObject` ("iso to the image of a bounded complex", line 1121);
  `BoundedHomotopyCategory := (boundedHomotopyObject C).FullSubcategory` (line 1165);
  `homotopyQuotientBounded := (boundedHomotopyObject C).lift …` (line 1178).
- Conditional triangulation of the bounded homotopy category via mathlib's
  full-subcategory machinery, gated on `(boundedHomotopyObject C).IsTriangulatedClosed₂`
  (lines 1749, 1760). **The project never proved `IsTriangulatedClosed₂` for
  `boundedHomotopyObject` unconditionally** — that is your milestone 5, and it is pure
  boundedness bookkeeping (a cone of a map between bounded complexes is bounded; every
  triangle is isomorphic to a cone triangle), independent of any acyclicity.
- Chain-vs-trW comparison, legacy shape (lines 2135, 2146):
  `boundedExactWeakEquivalence ≤ / = trW.inverseImage (homotopyQuotient C)` —
  your milestone 8 proves the corrected analogue.

Mirroring rule: copy the SHAPE (definitions, statement forms, proof skeletons);
substitute corrected predicates; never import a legacy theorem as a lemma in a
corrected proof.

## 6. Milestone ladder

Iteration protocol, every milestone: (1) one theorem/instance cluster, (2) the touched
files and `LeanLCAExactChallenge.lean` pass `lean -j1` (remember the olean trap, §3),
(3) run the §8 checklist, (4) one audit update (`audit/REPORT.md` new section +
`audit/NEXT_STEPS.md` completed-milestones list), (5) one commit, (6) fast-forward push
(§7). Small is beautiful; if a milestone fights back, split it.

**M1 — DONE** (`0483f25f`): `IsIdempotentComplete MetrizableLCA.{u}`.

**M2 — DONE** (`4c068b42`): contractible ⇒ corrected-acyclic.
`exactAcyclicWithCycles_of_contractingHomotopy` proved at general exact-category level
(`[Preadditive C] [QuillenExactCategory C] [IsIdempotentComplete C]` — no biproducts
needed) plus the MetrizableLCA corollary, in
`Derived/ExactAcyclicWithCyclesContractible.lean`. The proof is the pattern described
in §6's original sketch: `Homotopy.comm` gives `𝟙 = dNext + prevD` degreewise; the two
summands are orthogonal idempotents (`d ≫ d = 0` kills the cross terms and `p + q = 𝟙`
forces idempotency); `IsIdempotentComplete.idempotents_split` produces the cycle
objects; `QuillenExactCategory.split_conflation` (in `ExactCategory/Basic.lean` — a
split short complex is a conflation) gives the conflations; `d ≫ cycleEnd_{i+1} = d`
gives `d_eq`. Reuse this file as the template for how corrected-route proofs should
look: small named endomorphisms, `calc` chains, no `simp`-roulette on sensitive goals.

**M3 — homotopy invariance.** Statements:
`exactAcyclicWithCycles_of_homotopyEquiv : HomotopyEquiv K L → exactAcyclicWithCycles C K → exactAcyclicWithCycles C L`
and the corollary that homotopy equivalences of bounded complexes are corrected weak
equivalences (`boundedExactWeakEquivalenceWithCycles_of_homotopyEquiv`). Route: for a
homotopy equivalence `f`, `cone(f)` is contractible (find or prove the mathlib-level
fact; check `Homotopy`/`mappingCone` API in the pin), then M2 gives `cone(f)` acyclic;
for the K-acyclic ⇒ L-acyclic transfer you additionally need extension/2-out-of-3-style
closure, which overlaps M4 — sequence M3/M4 pragmatically: prove
"`f` htpy-equiv ⇒ `f ∈ W`" first (only needs M2), and full homotopy invariance of the
object predicate together with M4.

**M4 — cone closure (Bühler Lemma 10.3; the hardest single lemma).**
`exactAcyclicWithCycles (mappingCone f)` for `f : A ⟶ B` between corrected-acyclic
complexes. No idempotent-completeness hypothesis needed (§4.4). The cone sits in the
degreewise-split sequence `B ↪ cone(f) ↠ A[1]`; Bühler's proof constructs the cone's
cycle objects by pushout/pullback diagram lemmas from the cycle objects of `A` and `B`
(the admissible-morphism composition lemmas — check what
`ExactCategory/Basic.lean` provides; `MetrizableLCA`'s `HasFiniteLimits` can substitute
for missing pullback axioms in a specialized version). Budget the most time here.
Fallback if fully general Lean statements fight: prove it for `MetrizableLCA` only —
the final package only needs `MetrizableLCA`.

**M5 — bounded homotopy category is (pre)triangulated, unconditionally.**
Prove `(boundedHomotopyObject C).IsTriangulatedClosed₂` (for `C` with zero object +
binary biproducts, or just `MetrizableLCA`): in a triangle in `K(C)` with first two
vertices iso to images of bounded complexes, the third is too — realize the morphism by
a chain map of bounded representatives (fullness of the quotient), take its cone
(bounded), use uniqueness-up-to-iso of cones. Then the existing conditional
`boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2` (line 1749) becomes
unconditional instances. Independent of M2–M4; can be done in parallel or out of order.

**M6 — corrected acyclics are a triangulated ObjectProperty of `K^b`.**
Define (mirroring §5): `exactAcyclicWithCyclesHomotopyObject`, its iso-closure, and the
bounded restriction `(…IsoClosure).inverseImage (BoundedHomotopyCategory ι)`. Prove
`ObjectProperty.IsTriangulated` for it: contains zero (`exactAcyclicWithCycles_zero`),
shift-closed (closure file), closed₂ under triangles = M4 + M3 (iso-closure in `K^b`
needs homotopy invariance, which is where idempotent completeness earns its keep).
Then mathlib instances hand you `P.trW` calculus + triangulation compatibility free.

**M7 — bounded homotopy quotient is a localization.**
`(BoundedComplexCategory.homotopyQuotientBounded C).IsLocalization (bounded homotopy equivalences)`.
Mathlib has the unbounded statement
(`Mathlib/Algebra/Homology/Localization.lean:309`, generic form at `:263`); no bounded
version exists in the pin — mirror its proof (the cylinder-object argument restricts to
bounded complexes) or use the full-subcategory localization transfer if the pin has one.

**M8 — the comparison + factorization.**
(a) `boundedExactWeakEquivalenceWithCycles C = P.trW.inverseImage (homotopyQuotientBounded C)`
(mirror lines 2135/2146; the ≤ direction is near-definitional via the quotient-map
mapping-cone comparison; the ≥ direction uses M3 iso/homotopy-invariance).
(b) Hence `DboundedWithCycles.localization` inverts homotopy equivalences ⇒ factors
through `K^b`; `Functor.IsLocalization.of_comp` gives
`Lh : BoundedHomotopyCategory C ⥤ DboundedWithCycles C` with `Lh.IsLocalization P.trW`.
(c) `Lh.CommShift ℤ` via `commShiftOfLocalization` and the factorization iso.

**M9 — harvest + honest bridge restructuring + success flip.**
Apply the generic theorems (§4.2 step 4) to get `Preadditive`, `HasZeroObject`,
finite products (already have stability route too), `Pretriangulated`,
`IsTriangulated` on `DboundedWithCycles MetrizableLCA.{0}`. Add finite coproducts
(dual of the product route, or from biproducts once preadditive + products exist).
Then restructure `MetrizableStableBridgeWithCycles.lean`: new honest package (§4.3)
inhabited by proof; legacy-shaped `StablePackage`/`LeftCalculusAssumption` kept only as
explicitly-labeled compatibility surfaces; success marker flipped per §9; full audit
rewrite stating exactly what is proved and what remains legacy-shaped.

## 7. Git protocol

```bash
git status --short --branch          # expect only intended changes + the .lake symlink
git fetch origin main
git merge-base --is-ancestor origin/main HEAD && git push origin HEAD:main
```

Small commits, imperative subject, body says what was proved and how it was verified.
Never force-push. Never commit the `.lake` symlink or scratch files. If
`merge-base --is-ancestor` fails, someone moved `origin/main`: rebase-or-stop and
investigate — do not force anything.

## 8. Post-change review checklist (run every time, no exceptions)

1. `git status -sb` + read the full diff. Judge it like a hostile reviewer.
2. Legacy-backsliding grep over the diff (then whitelist by hand):

   ```bash
   git diff HEAD~1 | grep -nE "exactAcyclic|boundedExactWeakEquivalence|Dbounded|BoundedDerivedCategory|degreewiseConflationAcyclic|quasiIso" | grep -v "WithCycles"
   ```

   Anything that survives needs an explicit justification (compat artifact, comment,
   or legitimately unrelated). Especially damning: a corrected theorem proved by
   `simpa [exactAcyclic]` / `simpa [boundedExactWeakEquivalence]`.
3. Audit every `infer_instance` (and `inferInstance`) in the diff whose goal is one of
   `HasLeftCalculusOfFractions`, `Pretriangulated`, `IsTriangulated`, `HasFiniteLimits`,
   `HasFiniteColimits`: identify the exact instance Lean found (e.g. with
   `set_option trace.Meta.synthInstance true` in a scratch file). The failure mode is a
   legacy-route instance leaking through a synonym or unfolded abbreviation.
4. Forbidden tokens: `grep -n "sorry\|admit\|axiom\|unsafe" <touched files>` — empty.
5. Recompile touched modules' oleans, then `lean -j1` every touched file AND
   `lean -j1 LeanLCAExactChallenge.lean`. Exit 0 or it didn't happen.
6. Only after 1–5: audit update, commit, push.

## 9. The success marker

`currentMetrizableStableBridgeWithCyclesProductSuccessClaimed` is a deliberate honesty
device: it is `false` and has a theorem pinning it to `false`. Flip it (and its
theorem) in the SAME commit that lands the fully-inhabited corrected package — never
earlier, never in anticipation. A reviewer must be able to check out the flip commit
and verify the package is real by running §3 verification alone.

## 10. If you get blocked

Produce a blocker report (in `audit/`), not a success claim. Required contents: the
exact theorem/instance that blocked; the exact Lean error or missing declaration;
what was attempted (including failed proof strategies — they are data); what IS
Lean-proved so far; the smallest additional theorem, mathlib capability, or user
decision that would unblock. Then stop.

## 11. Known traps, in rough order of how much time they cost me

1. The olean staleness trap (§3). You will hit this on your first multi-file change.
2. Universe pinning: the bridge is typed against `MetrizableLCA.{0}` while most
   closure theorems are `.{u}`. Keep general statements `.{u}` and specialize late.
3. `BoundedComplexCategory` is a `FullSubcategory`; its morphisms unfold to morphisms
   of underlying complexes via `ι`. Statements about `W f` on the subcategory vs
   `mappingCone (ι.map f)` on ambient complexes — keep the `ι.map` explicit; several
   existing `Iff.rfl` bridges depend on the exact packaging.
4. Mathlib pin nomenclature: `ObjectProperty.trW` (not `Subcategory.W`);
   `Localization.preadditive`/`Triangulated.Localization.*` are generic in `L` — read
   the actual signatures in the pin before writing statements against them.
5. `Homotopy` API sign/direction conventions (`dNext`, `prevD`, `Homotopy.comm`) —
   derive the degreewise identity from `comm` in a scratch file first; do not guess.
6. ℤ-indexing off-by-ones in `ExactAcyclicWithCyclesData` (`Z (i+1)` vs `Z i`): decide
   the cycle-object indexing before writing the construction, or you will rewrite it.
7. The legacy `Dbounded` instances are still imported project-wide; when instance
   search behaves surprisingly, suspect them first (checklist §8.3).
8. `pgrep`-style self-matching and other shell footguns aside: general rule, verify
   claims with a command whose output you read, not with the absence of an error.

## 12. Current state ledger (as of this handover)

- Local branch @ `4c068b42` ("Prove contractible complexes are
  exactAcyclicWithCycles"); `origin/main` @ `0483f25f` at the moment of writing —
  push `4c068b42` fast-forward per §7 if the ledger check shows it unpushed.
- Milestones M1 (`0483f25f`) and M2 (`4c068b42`) done and verified green per §3 + §8.
- Audit files current through M2. `audit/NEXT_STEPS.md` lists remaining tasks and
  completed corrected milestones; `audit/REPORT.md` has the M1 and M2 sections and the
  version policy.
- Next up: M3 (homotopy equivalences are corrected weak equivalences — needs
  "cone of a homotopy equivalence is contractible", then M2 finishes it) and M4 (cone
  closure, the hardest lemma). M5 is independent and can be interleaved.
- Assumption surface remaining (the thing you are eliminating): chain-level left
  calculus (dissolves via §4.2), finite limits + finite colimits (resolve via §4.3),
  pretriangulated + triangulated (prove via M5–M9).

That's everything I know that the repo doesn't already say. The mathematics is sound,
the mathlib pin has every generic theorem you need, and the remaining work is honest
bricklaying along §6. Don't fake anything, verify everything twice, and flip the
marker last. — your predecessor
