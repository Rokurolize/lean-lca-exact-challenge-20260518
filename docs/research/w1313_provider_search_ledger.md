# W1313 Provider Search Ledger

W1313 inspects the W979 split/rebuild path around the W977 full-data provider.

W979 splits W977 full data into W971 component fields and rebuilds W977 data through W978. Its direct input surface is still one provider, so it does not reduce the current W1270 payload surface, which is also the single W987 full-data provider input. The W978 component-field reconstruction route expands to eighteen inputs.

Lean declarations `splitFullDataRebuildUsesComponentFieldsW1313` and `splitFullDataLeavesCarryRebuiltProviderW1313` record the checked split/rebuild path. The W979 boundary therefore documents a same-size cycle plus a larger component-field expansion, not a completion witness.

Product success is not claimed. The original four-task contract still lacks a product-success terminal outcome and review packet.
