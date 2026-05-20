import LeanLCAExactChallenge.LCA.ExactCategory
import LeanLCAExactChallenge.Derived.BoundedFiniteProducts
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Compactness.Compact

/-!
W296: the W229/W273 quasi-isomorphism transport bridge is false for the current
`MetrizableLCA` conflation predicate.

W273 reduces the direct identity-containment iso-closed input to transport of
`exactAcyclic MetrizableLCA` along `HomotopyEquiv`.  W229 gives a tempting route:
`HomotopyEquiv.toHomologyIso` gives degreewise `ShortComplex.QuasiIso`, so one might try to
transport `QuillenExactCategory.Conflation` across those short-complex quasi-isomorphisms.

That local bridge is too strong for the strict metrizable LCA exact structure.  The W256
counterexample `0 -> 0 -> 0` quasi-isomorphic to `0 -> 0 -> ZMod 2` proves that strict exactness,
and hence the concrete `QuillenExactCategory.Conflation`, is not invariant under arbitrary
`ShortComplex.QuasiIso`.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace ShortComplexQuasiIsoConflationCounterexampleW296

/-- The generic W232 bridge, specialized to the concrete strict `MetrizableLCA` exact category. -/
abbrev MetrizableLCAQuasiIsoConflationTransport : Prop :=
  ∀ {S T : ShortComplex MetrizableLCA.{0}} (φ : S ⟶ T) [S.HasHomology] [T.HasHomology],
    QuillenExactCategory.Conflation S → ShortComplex.QuasiIso φ →
      QuillenExactCategory.Conflation T

local instance : TopologicalSpace (ZMod 2) := ⊥
local instance : DiscreteTopology (ZMod 2) := ⟨rfl⟩

/-- The discrete two-element LCA object used by the quasi-isomorphism transport obstruction. -/
abbrev Z2LCA : MetrizableLCA.{0} :=
  MetrizableLCA.of (ZMod 2)

/-- Strict source complex: the split zero short complex. -/
abbrev sourceComplex : ShortComplex MetrizableLCA.{0} where
  X₁ := MetrizableLCA.zeroObj
  X₂ := MetrizableLCA.zeroObj
  X₃ := MetrizableLCA.zeroObj
  f := 0
  g := 0
  zero := by simp

/-- Quasi-isomorphic target with non-surjective right endpoint. -/
abbrev targetComplex : ShortComplex MetrizableLCA.{0} where
  X₁ := MetrizableLCA.zeroObj
  X₂ := MetrizableLCA.zeroObj
  X₃ := Z2LCA
  f := 0
  g := 0
  zero := by simp

/-- The source is a split strict exact sequence. -/
def sourceSplitting : sourceComplex.Splitting where
  r := 0
  s := 0

theorem source_conflation :
    QuillenExactCategory.Conflation sourceComplex :=
  MetrizableLCA.split_strictShortExact sourceSplitting

/-- The zero map is a quasi-isomorphism because both middle homology objects are zero. -/
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

theorem target_not_conflation :
    ¬ QuillenExactCategory.Conflation targetComplex := by
  intro h
  exact target_g_not_surjective h.surjective

/--
The concrete strict transport theorem obtained from the generic bridge is exactly the theorem
refuted by W256.
-/
theorem no_metrizableLCA_quasiIsoConflationTransport :
    ¬ MetrizableLCAQuasiIsoConflationTransport := by
  intro h
  haveI : sourceComplex.HasHomology :=
    ShortComplex.exact_of_isZero_X₂ sourceComplex MetrizableLCA.zeroObj_isZero |>.hasHomology
  haveI : targetComplex.HasHomology :=
    ShortComplex.exact_of_isZero_X₂ targetComplex MetrizableLCA.zeroObj_isZero |>.hasHomology
  exact target_not_conflation (h (0 : sourceComplex ⟶ targetComplex)
    source_conflation quasiIso_zero_to_target)

/--
Therefore the W229/W273 route cannot close exact-acyclic homotopy invariance by postulating
plain short-complex quasi-isomorphism invariance of conflations.
-/
def quasiIsoConflationTransportCounterexampleStatus : List String :=
  ["false: ShortComplex.QuasiIso transports QuillenExactCategory.Conflation for MetrizableLCA",
    "reason: W256 gives a quasi-isomorphism from the strict zero complex to 0 -> 0 -> ZMod 2",
    "next: exactAcyclic HomotopyEquiv transport needs a weaker degreewise theorem, extra endpoint/topology data, or a different route"]

theorem quasiIsoConflationTransportCounterexampleStatus_count :
    quasiIsoConflationTransportCounterexampleStatus.length = 3 := rfl

section Checks

#check MetrizableLCAQuasiIsoConflationTransport
#check source_conflation
#check quasiIso_zero_to_target
#check target_not_conflation
#check no_metrizableLCA_quasiIsoConflationTransport
#check quasiIsoConflationTransportCounterexampleStatus
#check quasiIsoConflationTransportCounterexampleStatus_count
#check ShortComplex.quasiIso_iff
#check ShortComplex.isZero_homology_of_isZero_X₂
#check MetrizableLCA.split_strictShortExact

end Checks

end ShortComplexQuasiIsoConflationCounterexampleW296

end LeanLCAExactChallenge
