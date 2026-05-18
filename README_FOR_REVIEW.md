# レビュー用メモ

## 結論

この成果物はproduct successではない。更新後のgoalではsource-patch-needed handoffで完了できないため、このpacketは歴史的な調査証跡と未完了診断として読む。

このリポジトリでは、Lean/mathlibで次の境界まではコンパイル確認済みである。

- `ShortComplex`上の`QuillenExactCategory`インターフェイス
- 連続加法準同型を射にした`MetrizableLCA`の圏
- 閉埋め込み、開全射、忘却後の代数的kernel/cokernel条件を束ねたstrict short exact sequence述語
- split short complexがstrict short exact sequenceになることのLean証明
- strict short exact sequenceが`ShortComplex`の同型で保たれることのLean証明
- `MetrizableLCA`のpullbackを積の閉部分群として構成し、strict sequenceのpullback安定性まで進めたLean証明
- pushout安定性だけを明示的境界として残したexact-category interface
- `audit/RequiredDeclarations.lean`による公開宣言の検査
- `audit/blockers/`に置いた最小再現ファイル

一方、strictなmetrizable LCA列のpushout安定性、そのexact category上のYoneda Ext、bounded derived infinity-categoryの構成は、まだローカル実装が必要である。このgoalでは、これらを残したまま`update_goal(status="complete")`を呼んではならない。

## 評価文脈

今回のpacketは、日本語読者がCodexの調査経路を追えるようにすることも目的にしている。どの文献、mathlib API、検索結果、失敗した探索が方針を変えたかは`docs/research/reference_route_log.md`に記録した。Leanファイルだけを見て「何が証明済みで、何が足場か」を推測しなくてよいように、`docs/research/mathlib_gap_analysis.md`と`terminal_outcome/terminal_outcome.json`にも同じ境界を明示している。

## 検証

期待する検証コマンドは次のとおり。

```bash
lake build
scripts/audit_no_forbidden_lean_tokens.sh LeanLCAExactChallenge
lake env lean audit/RequiredDeclarations.lean
lake env lean audit/ProductSuccessDeclarations.lean
python3 audit/external_audit.py --root "$PWD" --terminal-outcome terminal_outcome/terminal_outcome.json
git diff --check
```

`run/verification.json`には、実行したコマンドとsource tree hashを記録している。`audit/ProductSuccessDeclarations.lean`は未完成部分を検出する赤いproduct契約であり、`audit/external_audit.py`も`product_success`以外のterminal outcomeを失敗させる。

## レビューpacket

レビューpacketは次の場所に生成される。

```text
packets/lean_lca_exact_category_challenge/
```

zipの最終SHA256はpacket外部のsidecarだけを権威ある値として扱う。packet内部の`manifest.json`、`README_FOR_REVIEW.md`、`terminal_outcome.json`には、zip自身の最終SHA256を権威ある証拠として入れていない。
