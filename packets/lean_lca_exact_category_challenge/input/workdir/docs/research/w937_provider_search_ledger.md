# W937 Provider Search Ledger

Run root: `/home/roku/codex-consultant-20260517/outputs/lean_lca_hourly_strategy_runs/20260526T160420Z_codex_parent_w937_endpoint_short_exact_unit_strict_exact_components_route`

Baseline: W936 commit `d3b49e670159ce7c2a2d33ff7e1f578a9a34745a`, with product success still false and 39 explicit route inputs remaining.

| Candidate | Expected Lean surface | Prior evidence | Decision |
| --- | --- | --- | --- |
| Strict unit-witness component route | Replace the unit mapping-cone witness field from degreewise `MetrizableLCA.strictShortExact` data to the four fields of `MetrizableLCA.StrictShortExact`: closed inclusion, open map, surjectivity, and algebraic exactness | `LCA/StrictExact.lean` defines `StrictShortExact` with exactly these four fields, and the W937 constructor probe compiled | Selected for W937. |
| Endpoint topology from endpoint `ShortExact` | Derive W936's endpoint closed-embedding/open-map fields directly from endpoint `ShortExact` | The endpoint `ShortExact` field remains categorical and does not by itself provide the topological closed-embedding/open-map fields required by the current route | Deferred. |
| Unit mapping-cone component construction | Construct the actual unit mapping-cone strict components instead of exposing them as a field | No current no-argument localized right-adjoint/unit mapping-cone construction was identified in this pass | Deferred. |
| Target compactness or target-difference route | Prove one of the target compactness, target-difference, or relation primitive fields outright | Current APIs still expose these as primitive provider boundaries; no direct proof path was identified before the W937 component bridge | Deferred. |

Validation target: `LeanLCAExactChallenge/Derived/ClosedMapTargetCompactNoUnivMembershipEndpointShortExactUnitStrictExactComponentsPrimitiveFieldRoute.lean`.
