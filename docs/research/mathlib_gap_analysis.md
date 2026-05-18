# mathlib gap analysis

## 終端評価

四部構成の定理全体は完成していない。strict metrizable LCA列がQuillen exact categoryをなす部分までは、ローカルLean証明としてコンパイル確認済みである。

- ローカルの`QuillenExactCategory`インターフェイスはコンパイルする。
- `MetrizableLCA`は連続加法準同型を射にしたbundleされた圏としてコンパイルする。
- strict short exact sequenceは、閉埋め込み、開全射、忘却後の代数的完全性を含む述語としてコンパイルする。
- split short complexがstrict short exact sequenceになること、strict short exact sequenceが`ShortComplex`の同型で保たれることはLeanで証明済みである。
- `MetrizableLCA`のpullback objectは、積の閉部分群として構成し、そのconeがlimitであること、片側の射が全射なら対応するpullback射影も全射になること、kernel側の代数的完全性と閉埋め込み性をpullbackへ移せること、strict sequenceのpullback安定性をLeanで証明済みである。
- 閉部分群による商`MetrizableLCA`を構成し、pushoutを`(X₂ × Y) / range (x ↦ (f x, -a x))`としてLeanで構成した。この関係部分群が閉であること、標準射`Y ⟶ pushout`が閉埋め込みであること、pushout余極限であること、元の`S.g`へ降りる余核写像が開写像・全射・代数的に完全であることを証明済みである。
- 目標のLCA exact-category instanceは、未証明の引数なしで`QuillenExactCategory MetrizableLCA`として利用できる。
- Extとderived categoryの宣言は、abelian category側の既存APIまたは構成interfaceの境界までしか確認していない。

## exact-category API

ローカルsource searchでは、mathlib内に`ExactCategory`というmodule名やQuillen exact category classは見つからなかった。そのため、`LeanLCAExactChallenge/ExactCategory/Basic.lean`に次の形をローカルinterfaceとして実装した。

- conflationをshort complexとして持つ。
- inflationとdeflationをconflationの第一射、第二射として取り出す。
- split short complexをconflationに入れる。
- inflationがpushoutで安定であることを要求する。
- deflationがpullbackで安定であることを要求する。

ローカルの確認ファイル:

- `audit/blockers/quasi_abelian_exact_category_api.lean`

## strict LCA安定性定理

このprojectは`MetrizableLCA.strictShortExact`を定義している。`LeanLCAExactChallenge/LCA/StrictExact.lean`では、split short complexからstrict short exact sequenceを作る補助定理と、strict short exact sequenceの同型不変性を証明した。`LeanLCAExactChallenge/LCA/Pullback.lean`では、`MetrizableLCA`のpullbackを積の閉部分群として構成し、全射と開写像性をpullback射影へ移す補題、kernel mapの代数的完全性移送、kernel mapの閉埋め込み移送、そしてcategorical pullbackでのstrict short exactnessまで証明した。`LeanLCAExactChallenge/LCA/Quotient.lean`では閉部分群による商が再び`MetrizableLCA`になることを証明した。`LeanLCAExactChallenge/LCA/Pushout.lean`では、明示的pushout、関係部分群`range (x ↦ (f x, -a x))`の閉性、標準射`Y ⟶ pushout`の閉埋め込み性、余極限性、余核写像の開全射性と代数的完全性、そしてcategorical pushoutでのstrict short exactnessまで証明した。これにより、次の宣言は未証明引数なしで利用できる。

```lean
LeanLCAExactChallenge.MetrizableLCA.quillenExactCategory
LeanLCAExactChallenge.MetrizableLCA.instQuillenExactCategory
```

ローカル証拠:

- `LeanLCAExactChallenge/LCA/Basic.lean`
- `LeanLCAExactChallenge/LCA/StrictExact.lean`
- `LeanLCAExactChallenge/LCA/Quotient.lean`
- `LeanLCAExactChallenge/LCA/Pullback.lean`
- `LeanLCAExactChallenge/LCA/Pushout.lean`
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

`terminal_outcome/terminal_outcome.json`は`product_complete=false`を保つ必要がある。後続のproduct-success goalでは、strict metrizable LCA exact category上にYoneda Extとbounded derived infinity-categoryのAPIを構築する必要がある。
