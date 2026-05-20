import LeanLCAExactChallenge.LCA.ExactCategory
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Compactness.Compact

/-!
W256 audit: `ShortComplex.QuasiIso` alone cannot transport strict exactness.

The target complex `0 -> 0 -> ZMod 2` has zero middle homology, so the zero map
from `0 -> 0 -> 0` is a short-complex quasi-isomorphism.  Its last map is not
surjective, hence the target is not a strict short exact sequence in `MetrizableLCA`.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace QuasiIsoNotStrictTransportCounterexampleW256

local instance : TopologicalSpace (ZMod 2) := ⊥
local instance : DiscreteTopology (ZMod 2) := ⟨rfl⟩

abbrev Z2LCA : MetrizableLCA.{0} :=
  MetrizableLCA.of (ZMod 2)

abbrev sourceComplex : ShortComplex MetrizableLCA.{0} where
  X₁ := MetrizableLCA.zeroObj
  X₂ := MetrizableLCA.zeroObj
  X₃ := MetrizableLCA.zeroObj
  f := 0
  g := 0
  zero := by simp

abbrev targetComplex : ShortComplex MetrizableLCA.{0} where
  X₁ := MetrizableLCA.zeroObj
  X₂ := MetrizableLCA.zeroObj
  X₃ := Z2LCA
  f := 0
  g := 0
  zero := by simp

def sourceSplitting : sourceComplex.Splitting where
  r := 0
  s := 0

theorem source_strict : MetrizableLCA.strictShortExact sourceComplex :=
  MetrizableLCA.split_strictShortExact sourceSplitting

theorem quasiIso_zero_to_target :
    ShortComplex.QuasiIso (0 : sourceComplex ⟶ targetComplex) := by
  rw [ShortComplex.quasiIso_iff]
  exact IsZero.isIso
    (ShortComplex.isZero_homology_of_isZero_X₂ sourceComplex MetrizableLCA.zeroObj_isZero)
    (ShortComplex.isZero_homology_of_isZero_X₂ targetComplex MetrizableLCA.zeroObj_isZero)
    (ShortComplex.homologyMap (0 : sourceComplex ⟶ targetComplex))

theorem target_g_not_surjective :
    ¬ Function.Surjective (targetComplex.g : targetComplex.X₂ → targetComplex.X₃) := by
  intro h
  rcases h (1 : ZMod 2) with ⟨x, hx⟩
  cases x
  norm_num at hx

theorem target_not_strict : ¬ MetrizableLCA.strictShortExact targetComplex := by
  intro h
  exact target_g_not_surjective h.surjective

theorem no_unconditional_quasiIso_strict_transport :
    ¬ (∀ {S T : ShortComplex MetrizableLCA.{0}} (φ : S ⟶ T)
        [S.HasHomology] [T.HasHomology],
        MetrizableLCA.strictShortExact S → ShortComplex.QuasiIso φ →
          MetrizableLCA.strictShortExact T) := by
  intro h
  exact target_not_strict
    (h (0 : sourceComplex ⟶ targetComplex) source_strict quasiIso_zero_to_target)

section Checks

#check Z2LCA
#check source_strict
#check quasiIso_zero_to_target
#check target_g_not_surjective
#check target_not_strict
#check no_unconditional_quasiIso_strict_transport

end Checks

end QuasiIsoNotStrictTransportCounterexampleW256

end LeanLCAExactChallenge
