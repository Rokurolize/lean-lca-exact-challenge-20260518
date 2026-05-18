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
- Extとderived categoryの宣言は、strict LCA exact categoryから使えるローカル構成に置き換えた。ただし、標準的なYoneda Extに必要な任意Baer sum witnessの構成、左側の商関係にも降りる双線形積、stable infinity-categoryとしての構造は未完成である。

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

mathlibはderived category API経由で、abelian categoryに対する`CategoryTheory.Abelian.Ext`を提供している。今回のローカル実装では、これを包むだけの定義をやめ、`QuillenExactCategory.Conflation`から一段拡大`ShortExactExtension`と有限の`YonedaExtension` chainを定義した。`YonedaExt X Y 0`は`X ⟶ Y`の`ULift`であり、正次数はextension chainを生成元とする自由加法可換群を`yonedaRelationSubgroup`で割った群である。これにより、`MetrizableLCA`のexact category instanceだけから`YonedaExt (C := MetrizableLCA)`が使える。

実装済みの商関係は、hom等式、endpointと中間対象の同型をたどるextension鎖の同型、分裂一段拡大を零元にする生成関係、split factorを含む鎖を零元にする生成関係、Baer sum witnessから来る生成関係である。さらに、分裂一段拡大とsplit factorを含む正次数鎖がExtの零元になり、Baer sum witnessがある場合に一段Extで`sum = e₁ + e₂`になること、公開APIの`baer_sum`も同じ結果を返すことを定理として証明した。正次数では、関係部分群に`sum - a - b`が入る任意のextension chainから同じ加法等式を取り出す汎用補題を追加し、一段Baer witnessを共通prefixで正次数鎖へ持ち上げるwitnessも扱える。一段拡大を左からspliceする写像については、関係部分群を保つことを証明し、商群`YonedaExt`上の加法準同型`leftProductByExtension`として降ろした。また、左からspliceする一段拡大が分裂している場合、その積の値が0になることも証明した。さらに、純粋な一段拡大列からなる`PositiveChain`を固定した左spliceも、右側の関係部分群を保つ加法準同型`leftProductByPositiveChain`として降ろした。残る不足は、標準的なYoneda Extで必要な構成のうち、任意の一段拡大対に対してBaer sum witnessを構成する部分、左側の商関係にも降りる双線形Yoneda積、degree 0や任意のhom尾部を含む長さ方向の関係を完全には実装していない点である。したがって現在の`YonedaExt`は「exact categoryから定義された局所的なYoneda chain商群」であり、通常の意味のYoneda Ext群と同一視するには追加実装が必要である。

最小のコンパイル確認済み再現:

- `audit/blockers/yoneda_ext_exact_category_api.lean`

## bounded derived infinity-categoryの不足

mathlibはabelian categoryに対して`DerivedCategory C`を提供している。要求されたexact categoryのbounded derived infinity-category `D^b(C,E)`は、確認したローカルAPIでは直接の構成として利用できなかった。

今回のローカル実装では、`MetrizableLCA`のbinary biproductを積で構成し、cochain complexのmapping coneを使えるようにした。そのうえで、bounded cochain complexのfull subcategoryと、mapping coneがexact acyclicである射からなるmorphism propertyを定義し、mathlibのlocalization APIでlocalizeした。

露出している主な宣言は次である。

- `LeanLCAExactChallenge.boundedCochainComplex`;
- `LeanLCAExactChallenge.exactAcyclic`;
- `LeanLCAExactChallenge.boundedExactWeakEquivalence`;
- `LeanLCAExactChallenge.BoundedDerivedInfinityCategory`;
- `LeanLCAExactChallenge.Dbounded`;
- `LeanLCAExactChallenge.Dbounded.localization`.

残る不足は、これがordinary categoryのlocalizationであり、stable infinity-categoryそのものを表すlocal model structureやsimplicial/infinity-categorical enhancementではない点である。goalの「bounded derived infinity-category」を厳密に読むなら、この不足はproduct gapとして残る。

最小のコンパイル確認済み再現:

- `audit/blockers/derived_infinity_exact_category_api.lean`

## product completionの境界

`terminal_outcome/terminal_outcome.json`は`product_complete=false`を保つ必要がある。後続のproduct-success goalでは、標準的なYoneda ExtのBaer sum witness構成、左側の商関係にも降りる双線形Yoneda積、degree 0やhom尾部を含む積の互換性、また`D^b(C,E)`をordinary localization以上の意味で扱うためのinfinity-category側のモデルを実装する必要がある。
