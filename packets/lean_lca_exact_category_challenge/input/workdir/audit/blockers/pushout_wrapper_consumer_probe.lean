import LeanLCAExactChallenge.Ext.Yoneda

/-!
Downstream consumer probe for the explicit pushout kernel/range wrapper.

This file intentionally imports only the Yoneda extension layer. The probe
checks that a Yoneda-facing one-fold pushout extension can recover the kernel
of its tail map as the range of the pushed-out kernel injection without adding
a direct `LCA.Pushout` import at the call site.
-/

set_option autoImplicit false

universe u

namespace LeanLCAExactChallenge

open CategoryTheory

namespace MetrizableLCA

example {X Y Y' : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (a : Y ⟶ Y')
    (q : (shortExactExtensionPushout e a).middle) :
    (shortExactExtensionPushout e a).p q = 0 ↔
      ∃ y : Y', (shortExactExtensionPushout e a).i y = q := by
  exact shortExactExtensionPushout_kernel_iff_range_i e a q

#check shortExactExtensionPushout
#check shortExactExtensionPushout_kernel_iff_range_i
#check pushoutCokernelMap_kernel_iff_range_inr

end MetrizableLCA

end LeanLCAExactChallenge
