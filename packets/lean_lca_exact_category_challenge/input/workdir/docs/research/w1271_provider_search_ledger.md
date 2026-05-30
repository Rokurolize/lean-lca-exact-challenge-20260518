# W1271 Provider Search Ledger

Date: 2026-05-29

W1271 inspects the tempting W999 route after W1270 reduced the active surface to one W987 branch-full-data provider.

Relevant declarations:

1. `currentFullDataPayloadOfBranchFullDataW1270` constructs W977 current full-data payload from W987 branch full data.
2. `branchFullDataOfCurrentFullDataW999` constructs W987 branch full data from W977 current full data.
3. `currentFullDataInputNamesW999_count` and `currentFullDataPayloadFromBranchFullDataInputNamesW1270_count` both prove one explicit input.

Conclusion: W999 does not discharge the final W987 provider. It forms a one-input cycle with W1270, returning to the same W977 payload boundary that W1270 is trying to construct. Product success remains false.
