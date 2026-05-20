# Initial Mathlib Survey

Prepared by the consultant setup before assigning the goal.

Baseline toolchain:

```text
leanprover/lean4:v4.30.0-rc2
mathlib v4.30.0-rc2
```

Useful existing APIs:

- `TopCat` and `TopCat.Hom` for bundled topological spaces and continuous maps.
- `AddCommGrpCat` and `AddCommGrpCat.Hom` for bundled additive commutative groups.
- `AddGroupTopology` and `LocallyCompactSpace` for topological group and local compactness structure.
- `CategoryTheory.ShortComplex` and `CategoryTheory.ShortComplex.Exact` for exactness of short complexes.
- `CategoryTheory.DerivedCategory` and `CategoryTheory.Abelian.Ext` for abelian-category derived categories and Ext groups.

The setup search did not find a mathlib module named `ExactCategory` or a direct Quillen exact-category API. The worker should verify this against current local source before designing the exact-category layer.

Known local commands that passed before assignment:

```bash
lake build
scripts/check_mathlib_survey.sh
scripts/audit_no_forbidden_lean_tokens.sh LeanLCAExactChallenge
```
