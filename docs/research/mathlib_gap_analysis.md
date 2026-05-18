# mathlib gap analysis

## 終端評価

四部構成の定理全体は完成していない。このリポジトリでコンパイル確認できた最も強い境界はsource-patch-needed handoffである。

- ローカルの`QuillenExactCategory`インターフェイスはコンパイルする。
- `MetrizableLCA`は連続加法準同型を射にしたbundleされた圏としてコンパイルする。
- strict short exact sequenceは、閉埋め込み、開全射、忘却後の代数的完全性を含む述語としてコンパイルする。
- 目標のexact-category instanceは、明示的な`StrictExactQuillenAxioms`からだけ構成される。
- Extとderived categoryの宣言は、abelian category側の既存APIまたは構成interfaceの境界までしか確認していない。

## exact-category APIの不足

ローカルsource searchでは、mathlib内に`ExactCategory`というmodule名やQuillen exact category classは見つからなかった。そのため、`LeanLCAExactChallenge/ExactCategory/Basic.lean`に次の形をローカルinterfaceとして記録した。

- conflationをshort complexとして持つ。
- inflationとdeflationをconflationの第一射、第二射として取り出す。
- inflationがpushoutで安定であることを要求する。
- deflationがpullbackで安定であることを要求する。

最小のコンパイル確認済み再現:

- `audit/blockers/quasi_abelian_exact_category_api.lean`

## strict LCA安定性定理の不足

このprojectは`MetrizableLCA.strictShortExact`を定義している。しかし、これらのstrict sequenceがQuillen exact-category公理を満たすという定理は、確認したmathlib APIからは利用できなかった。handoff境界は次の宣言である。

```lean
LeanLCAExactChallenge.MetrizableLCA.StrictExactQuillenAxioms
LeanLCAExactChallenge.MetrizableLCA.quillenExactCategory
```

後者は前者を明示的な引数として要求するため、未証明のproduct theoremを完成済みinstanceとして包んでいない。

ローカル証拠:

- `LeanLCAExactChallenge/LCA/Basic.lean`
- `LeanLCAExactChallenge/LCA/StrictExact.lean`
- `LeanLCAExactChallenge/LCA/ExactCategory.lean`

## exact category上のYoneda Extの不足

mathlibはderived category API経由で、abelian categoryに対する`CategoryTheory.Abelian.Ext`を提供している。このリポジトリでは、そのコンパイル確認済み境界を`LeanLCAExactChallenge.YonedaExt`として露出した。

不足しているのは、一般のQuillen exact category上のYoneda Ext構成と、それをstrict metrizable LCA conflationへ特殊化するAPIである。

最小のコンパイル確認済み再現:

- `audit/blockers/yoneda_ext_exact_category_api.lean`

## bounded derived infinity-categoryの不足

mathlibはabelian categoryに対して`DerivedCategory C`を提供している。要求されたexact categoryのbounded derived infinity-category `D^b(C,E)`は、確認したローカルAPIでは直接の構成として利用できなかった。

このリポジトリで露出しているのは次の境界である。

- `LeanLCAExactChallenge.BoundedDerivedInfinityCategory`, a construction interface requiring an exact category;
- `LeanLCAExactChallenge.Dbounded`, the underlying type of a chosen construction;
- `LeanLCAExactChallenge.abelianDerivedCategory`, 確認済みのabelian-category比較対象。

最小のコンパイル確認済み再現:

- `audit/blockers/derived_infinity_exact_category_api.lean`

## product completionの境界

`terminal_outcome/terminal_outcome.json`は`product_complete=false`を保つ必要がある。後続のproduct-success goalでは、明示的なLCA source-patch仮定をLeanで証明済みの宣言に置き換え、そのexact category上にYoneda Extとbounded derived infinity-categoryのAPIを構築する必要がある。
