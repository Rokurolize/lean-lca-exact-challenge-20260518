# Proof Frontier Matrix

Generated: 2026-05-18T23:12:39Z

Current active thread: `019e3c1e-ce8e-7190-9df0-18452cc5e187`.

No workers are launched now. The governor goal says not to run concurrently against a dirty target worktree owned by another active process; this session is the active parent process and owns the current dirty proof-frontier edits.

| frontier_id | target | allowed writes | verification | merge blocker | product contribution | owner |
| --- | --- | --- | --- | --- | --- | --- |
| `frontier-left-yoneda-descent` | left-variable quotient descent and bilinear Yoneda product compatibility | `Ext/Yoneda.lean`, audits, docs/evidence | `lake env lean audit/blockers/yoneda_ext_exact_category_api.lean` | active dirty parent worktree | required for standard Yoneda product on quotient Ext groups | active parent |
| `frontier-degree0-hom-tail` | degree 0 head/tail compatibility, including pullback head, pushout tail, split pullback/pushout preservation, and split-zero Ext lemmas | `Ext/Yoneda.lean`, Yoneda audits | `lake build && lake env lean audit/ProductSuccessDeclarations.lean` | generator-level head pullback, arbitrary tail pushout, split pullback/pushout preservation, split-zero Ext lemmas, tail pushout preservation of right-split/split-factor zero generators, and composeTailHom preservation of iso generators are implemented; quotient descent remains | required for degree-zero Yoneda composition compatibility | active parent |
| `frontier-dbounded-infinity` | stable infinity-category enhancement or product-approved tightening | `Derived/Bounded.lean`, product audit | `lake env lean audit/blockers/derived_infinity_exact_category_api.lean` | ordinary localization is not enough for product truth | required for fourth objective | unassigned |
| `frontier-audit-hardening` | external audit and product declarations reject placeholders | `audit/external_audit.py`, `audit/ProductSuccessDeclarations.lean` | `python3 audit/external_audit.py --root "$PWD" --terminal-outcome terminal_outcome/terminal_outcome.json` | must not weaken product gate | prevents false product claims | unassigned |
| `frontier-route-log` | Japanese route log, gap analysis, packet consistency | docs, manifest/evidence, packets | external audit plus packet clean extraction | refresh after proof changes | required for reviewability | active parent |
