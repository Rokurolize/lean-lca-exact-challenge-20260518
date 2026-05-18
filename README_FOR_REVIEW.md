# レビュー用メモ

## 結論

この成果物はproduct successではない。更新後のgoalではsource-patch-needed handoffで完了できないため、このpacketは歴史的な調査証跡と未完了診断として読む。

このリポジトリでは、Lean/mathlibで次の境界まではコンパイル確認済みである。

- `ShortComplex`上の`QuillenExactCategory`インターフェイス
- 連続加法準同型を射にした`MetrizableLCA`の圏
- 閉埋め込み、開全射、忘却後の代数的kernel/cokernel条件を束ねたstrict short exact sequence述語
- split short complexがstrict short exact sequenceになることのLean証明
- strict short exact sequenceが`ShortComplex`の同型で保たれることのLean証明
- strict short exact sequenceがcoordinatewise binary biproductで保たれることのLean証明
- `MetrizableLCA`のpullbackを積の閉部分群として構成し、strict sequenceのpullback安定性まで進めたLean証明
- 閉部分群による商`MetrizableLCA`、および`(X₂ × Y) / range (x ↦ (f x, -a x))`としての明示的pushoutを構成し、関係部分群の閉性、標準射`Y ⟶ pushout`の閉埋め込み性、余極限性、余核側の開全射・代数的完全性まで進めたLean証明
- strictなmetrizable LCA列をconflationとする`QuillenExactCategory MetrizableLCA` instance
- `MetrizableLCA`のbinary biproductを積で構成し、mapping coneに必要な`HasBinaryBiproducts MetrizableLCA` instanceと、strict sequenceのbiproduct安定性
- `MetrizableLCA`の一段拡大2つからcoordinatewise product extensionを作り、明示的な積モデルからmathlibのchosen binary biproduct端点へ移送するLean定理。さらにそのproduct extensionを対角pullbackと余対角pushoutへ通し、任意の一段拡大対に対する標準的な`BaerSumData`をLeanで構成している
- exact categoryのconflation chainから作るローカル`YonedaExt`型。degree 0はHom、正次数はconflation chainを生成元とする自由加法可換群を、extension鎖の同型、hom等式、分裂一段拡大、split factorを含む鎖、Baer sum witness、hom tail pushout witnessから来る生成関係で割った群としてコンパイルする。分裂一段拡大とsplit factorを含む正次数鎖が0になり、Baer sum witnessがある場合に`sum = e₁ + e₂`となり、公開APIの`baer_sum`も同じ結果を返すことをLean定理として確認している。さらに、正次数の関係部分群に`sum - a - b`が入る任意のextension chainについて、`sum = a + b`と`baer_sum a b = sum`を返す汎用補題を追加し、一段拡大を左からspliceする写像が商群`YonedaExt`へ降りること、左からspliceする一段拡大が分裂していれば積の値が0になること、純粋な一段拡大列からなる正次数鎖を固定した左spliceが右側の商群へ降りること、その固定左鎖に分裂因子があれば積が0になること、左端一段拡大の同型関係とBaer和を固定tailの前へ貼っても等式・加法等式・`baer_sum`等式が得られること、一段拡大の後ろにdegree 0のhom tailが付く一段ケースをpushout拡大へ落とす等式も確認した
- bounded cochain complexのfull subcategoryを、mapping coneがexact acyclicである射でlocalizeする`Dbounded`構成
- `audit/RequiredDeclarations.lean`による公開宣言の検査
- `audit/blockers/`に置いた最小再現ファイル

一方、標準的なYoneda Extとして必要な構成のうち、左側の商関係全体にも降りる双線形なYoneda積、degree 0のpullback側の作用、任意長のhom tailを含む長さ方向の関係を完全に扱う部分は未完成である。また`Dbounded`はordinary categoryのlocalizationとしては構成したが、stable infinity-categoryそのもののモデルではない。このgoalでは、これらを残したまま`update_goal(status="complete")`を呼んではならない。

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

`run/verification.json`には、実行したコマンドとsource tree hashを記録している。`audit/ProductSuccessDeclarations.lean`は現在の公開APIがstrict LCA exact categoryから使えることを確認する。`audit/external_audit.py`はgoalの完了条件どおり、`product_success`以外のterminal outcomeを失敗させる。

## レビューpacket

レビューpacketは次の場所に生成される。

```text
packets/lean_lca_exact_category_challenge/
```

zipの最終SHA256はpacket外部のsidecarだけを権威ある値として扱う。packet内部の`manifest.json`、`README_FOR_REVIEW.md`、`terminal_outcome.json`には、zip自身の最終SHA256を権威ある証拠として入れていない。
