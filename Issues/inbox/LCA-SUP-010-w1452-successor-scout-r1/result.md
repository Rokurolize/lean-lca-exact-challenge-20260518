# LCA-SUP-010 W1452 Successor Route Scout

Status: accepted_candidate

Observed target head: `3b4cf5906e2ebead9b5ea0b6e01a15cbaccae251`

Product success claimed: false

## Decision

Recommend targeting W984 internals next. The next useful Lean increment should replace W1452's carried `TargetNoUnivClosedEmbeddingClosednessDataProviderW984` input with the two W1440/W1300 fields: W944 target-no-univ data and W973 closed-embedding closedness data. It should keep the W1452 raw W716/W717 fields and the carried W950 provider, construct W984 from W944/W973, then feed that result through the existing W1452/W1451/W1450 W987 construction.

This reduces the current frontier because W1451 already split W716 into raw boundary fields and W1452 already split W717 into raw relation fields. The remaining bundled provider assumptions at the W1452 surface are W984 and W950; W1440 gives the source-backed two-field W984 split, so it is the most direct non-duplicate successor.

## Evidence

- `W1452` constructs W717 from raw relation-pullback and target-relation-lifts providers, then runs W1451, with projections back to raw relation fields, raw boundary fields, and carried W984/W950 data: `LeanLCAExactChallenge/Derived/...W1452.lean` lines 21, 228, 255, and 258.
- `W1452` remains nonterminal and proves `productSuccessClaimed=false`: `LeanLCAExactChallenge/Derived/...W1452.lean` line 265.
- `W1450` names the still-bundled W987 construction inputs as W716, W717, W984, and W950: `LeanLCAExactChallenge/Derived/...W1450.lean` line 126.
- `W1451` already split W716 into raw right-open and source-pi-zero boundary fields: `LeanLCAExactChallenge/Derived/...W1451.lean` line 201.
- `W1440` records that W984 unpacks to W944 target no-univ data and W973 closed-embedding closedness data: `LeanLCAExactChallenge/Derived/...W1440.lean` lines 95 and 139.
- `W1441` makes W950 internals viable as a secondary route, but it is not the first choice here: `LeanLCAExactChallenge/Derived/...W1441.lean` line 83.
- `docs/research/reference_route_log.md` line 1393 confirms W1452 split W717 while leaving W984/W950 plus raw W716/W717 assumptions and no product-success claim.
- `terminal_outcome/terminal_outcome.json` and `run/verification.json` report product success false for W1452.

## Rejected Routes

- Remaining raw W716/W717 assumptions: duplicate of W1451/W1452 field splitting rather than a new frontier reduction.
- W950 internals: viable second choice, but W984 has an earlier direct two-field target/closedness split already available from W1440.
- Final product witness surface: too broad for the next small increment, and the audit state still lacks a positive `OriginalFourTaskProductSuccess` witness.
- Metadata freshness: the observed target head matches the W1452 base head, and the target worktree is clean.
- W1440-W1449 wrapper, unpack, provider-packaging, and rewrap cycles: already documented as nonterminal or rejected.

## Candidate Next Action

Create a W1453-style nonterminal guard that takes the W1452 raw W716/W717 fields, replaces the carried W984 provider with W944 and W973 fields, constructs W984 through the existing W1300/W1440 route, then feeds that W984 plus carried W950 into the W1452/W1451/W1450 construction. Prove projections back to W944/W973, W950, and the raw W716/W717 fields, and keep `productSuccessClaimed=false`.

Suggested Lean command for the parent/implementation context:

```bash
lake env lean LeanLCAExactChallenge/Derived/ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataW987BoundaryRelationFieldDataConstructionGuardW1452.lean
```
