# Stable Product Review Gate Map W93

The current repository has two separate review layers for stable bounded-derived infinity-category product success.

First, `audit/external_audit.py` is the packet-level rejection layer. In `check_derived_infinity_product_contract`, it rejects a product-success terminal outcome when `BoundedDerivedInfinityCategory` is still the ordinary nerve of the localized category, when no stable marker appears in `Derived/Bounded.lean`, when `audit/ProductSuccessDeclarations.lean` does not check stable evidence, or when a stable certificate name appears without field evidence for finite limits, finite colimits, suspension/loop equivalence, and pushout/pullback compatibility. The negative fixtures exercised by `check_negative_fixture` keep marker-only and ordinary-nerve-only packets from passing review.

Second, the future Lean semantic layer should be owned by `audit/ProductSuccessDeclarations.lean`, not by `terminal_outcome/terminal_outcome.json`. `terminal_outcome/terminal_outcome.json` should only report the result after Lean and external audit evidence exists. `audit/RequiredDeclarations.lean` is useful as a symbol inventory, but it should not be the first durable owner of the product gate because `#check` lines alone do not consume a stable certificate.

The proposed gate order is:

1. `audit/external_audit.py` rejects packet-level marker-only, ordinary-nerve-only, and certificate-name-only claims.
2. `LeanLCAExactChallenge/Derived/Bounded.lean` eventually exposes a real stable certificate API for `Dbounded.infinityCategory`.
3. `audit/ProductSuccessDeclarations.lean` consumes that API and projects all four fields: `finiteLimits`, `finiteColimits`, `suspensionLoopEquivalence`, and `pushoutPullbackCompatibility`.
4. `terminal_outcome/terminal_outcome.json` may then use product-success wording only after the declarations and verification record cover the stable projection check.

The companion Lean skeleton `audit/blockers/stable_product_review_gate_map_w93.lean` encodes this review boundary without claiming product success. It maps the current `Dbounded.infinityNerve_quasicategory` evidence to an explicit ordinary-nerve rejection branch, and gives the future pass branch only a `FourStableProjectionEvidence` value with all four projections available.

This keeps the W85/W90 boundary intact: external audit is a necessary negative gate, while `audit/ProductSuccessDeclarations.lean` is the first durable positive owner once real stable projection evidence exists.
