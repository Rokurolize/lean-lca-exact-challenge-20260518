import LeanLCAExactChallenge.Ext.Yoneda

/-!
W84 smoke for the production-style, unsuffixed Yoneda positive cast API.

This file intentionally does not redeclare the cast or associativity names. It checks
that downstream code can consume the public `YonedaExt` declarations.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

universe u

#check YonedaExt.positiveYonedaExtCast
#check YonedaExt.positiveYonedaExtCast_ofExtension
#check YonedaExt.positiveYonedaExtCast_spliceLeftWith_assoc
#check YonedaExt.yonedaProduct_ofExtension_assoc_cast

namespace YonedaUnsuffixedPortSmokeW84

theorem w54_bridge_replaced_by_unsuffixed_assoc_cast
    {X W Y Z : MetrizableLCA.{u}} {m n l : ℕ}
    (a : YonedaExtension (C := MetrizableLCA.{u}) X W (m + 1))
    (b : YonedaExtension (C := MetrizableLCA.{u}) W Y (n + 1))
    (c : YonedaExtension (C := MetrizableLCA.{u}) Y Z (l + 1))
    (hdeg : l + (n + (m + 1) + 1) = (l + (n + 1)) + (m + 1)) :
    YonedaExt.positiveYonedaExtCast (C := MetrizableLCA.{u}) (X := X) (Y := Z) hdeg
        (YonedaExt.yonedaProduct (X := X) (Y := Y) (Z := Z) (n + (m + 1)) l
          (YonedaExt.yonedaProduct (X := X) (Y := W) (Z := Y) m n
            (YonedaExt.ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := W) (n := m) a)
            (YonedaExt.ofExtension (C := MetrizableLCA.{u}) (X := W) (Y := Y) (n := n) b))
          (YonedaExt.ofExtension (C := MetrizableLCA.{u}) (X := Y) (Y := Z) (n := l) c)) =
      YonedaExt.yonedaProduct (X := X) (Y := W) (Z := Z) m (l + (n + 1))
        (YonedaExt.ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := W) (n := m) a)
        (YonedaExt.yonedaProduct (X := W) (Y := Y) (Z := Z) n l
          (YonedaExt.ofExtension (C := MetrizableLCA.{u}) (X := W) (Y := Y) (n := n) b)
          (YonedaExt.ofExtension (C := MetrizableLCA.{u}) (X := Y) (Y := Z) (n := l) c)) := by
  exact YonedaExt.yonedaProduct_ofExtension_assoc_cast
    (a := a) (b := b) (c := c) (hdeg := hdeg)

end YonedaUnsuffixedPortSmokeW84

end LeanLCAExactChallenge
