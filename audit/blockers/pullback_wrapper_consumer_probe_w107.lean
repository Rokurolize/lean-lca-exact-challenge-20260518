import LeanLCAExactChallenge.Ext.Yoneda

/-!
Consumer smoke for the strict short-exact pullback wrapper.

This checks that downstream Yoneda/LCA users can consume the one-fold extension
pullback API through `ShortExactExtension.PullbackData`, without reopening the
explicit `pullbackObj` proof in `LCA.Pullback`.
-/

set_option autoImplicit false

universe u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace MetrizableLCA

noncomputable example {X X' Y : MetrizableLCA.{u}} (e : ShortExactExtension X Y) (a : X' ⟶ X) :
    ShortExactExtension.PullbackData e a (shortExactExtensionPullback e a) :=
  shortExactExtensionPullbackData e a

noncomputable example {X X' Y : MetrizableLCA.{u}} (e : ShortExactExtension X Y) (a : X' ⟶ X) :
    (shortExactExtensionPullback e a).i ≫ pullbackSnd a e.p = e.i :=
  shortExactExtensionPullback_i_map e a

noncomputable example {X X' Y : MetrizableLCA.{u}} (e : ShortExactExtension X Y) (a : X' ⟶ X) :
    pullbackSnd a e.p ≫ e.p = (shortExactExtensionPullback e a).p ≫ a :=
  shortExactExtensionPullback_map_p e a

noncomputable example {X X' Y : MetrizableLCA.{u}} (e : ShortExactExtension X Y) (a : X' ⟶ X) :
    QuillenExactCategory.Conflation (shortExactExtensionPullback e a).shortComplex :=
  (shortExactExtensionPullback e a).conflation

#check shortExactExtensionPullback
#check shortExactExtensionPullbackData
#check strictShortExact_pullback
#check strictShortExact_categorical_pullback

end MetrizableLCA

end LeanLCAExactChallenge
