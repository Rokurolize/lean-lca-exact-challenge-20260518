import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.Single

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

/-- Degreewise right-unbounded nonzero support for the concrete-tail scout. -/
abbrev ConcreteTailHasUpperUnboundedNonzeroTerms
    (C : Type u) [Category.{v} C] [Preadditive C] (K : CochainComplex C ℤ) : Prop :=
  ∀ b : ℤ, ∃ i : ℤ, b < i ∧ ¬ IsZero (K.X i)

/-- Minimal data needed to turn the w86 frontier into an actual counterexample. -/
structure ConcreteUnboundedContractibleTail
    (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C] where
  tail : CochainComplex C ℤ
  tail_upper_unbounded : ConcreteTailHasUpperUnboundedNonzeroTerms C tail
  tail_contractible :
    ∃ Z : CochainComplex C ℤ,
      Z = 0 ∧
        Nonempty (@HomotopyEquiv ℤ C _ _ (ComplexShape.up ℤ)
          (show HomologicalComplex C (ComplexShape.up ℤ) from tail)
          (show HomologicalComplex C (ComplexShape.up ℤ) from Z))

namespace ContractibleTailConcreteScout

/-- `ℤ` is a usable nonzero object for an `AddCommGrpCat` tail. -/
lemma addCommGrp_int_not_isZero : ¬ IsZero (AddCommGrpCat.of ℤ) := by
  intro h
  have hid_zero : (𝟙 (AddCommGrpCat.of ℤ) : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ) = 0 :=
    h.eq_of_src _ _
  have h_apply := congrArg (fun f : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ => f (1 : ℤ)) hid_zero
  norm_num at h_apply

/-- `ModuleCat ℤ` has the same concrete nonzero object candidate. -/
lemma moduleCat_int_not_isZero : ¬ IsZero (ModuleCat.of ℤ ℤ) := by
  intro h
  have hid_zero : (𝟙 (ModuleCat.of ℤ ℤ) : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ) = 0 :=
    h.eq_of_src _ _
  have h_apply := congrArg (fun f : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ => f (1 : ℤ)) hid_zero
  norm_num at h_apply

example : HasProduct (fun _ : ℕ => AddCommGrpCat.of ℤ) := by
  infer_instance

example : HasCoproduct (fun _ : ℕ => AddCommGrpCat.of ℤ) := by
  infer_instance

example : HasProduct (fun _ : ℕ => ModuleCat.of ℤ ℤ) := by
  infer_instance

example : HasCoproduct (fun _ : ℕ => ModuleCat.of ℤ ℤ) := by
  infer_instance

/-- The first bridge still missing after API inspection: a constructor for a concrete
right-unbounded contractible cochain complex over one of the simple additive categories. -/
abbrev AddCommGrpConcreteTailConstructor : Prop :=
  Nonempty (ConcreteUnboundedContractibleTail AddCommGrpCat.{0})

/-- The analogous module-category constructor. -/
abbrev ModuleCatIntConcreteTailConstructor : Prop :=
  Nonempty (ConcreteUnboundedContractibleTail (ModuleCat.{0} ℤ))

#check AddCommGrpCat.of
#check AddCommGrpCat.biproductIsoPi
#check AddCommGrpCat.hasColimitsOfShape
#check ModuleCat.of
#check ModuleCat.hasLimits
#check (inferInstance : HasFiniteColimits (ModuleCat.{0} ℤ))
#check HomologicalComplex.single
#check HomologicalComplex.singleObjXSelf
#check CochainComplex
#check Homotopy
#check HomotopyEquiv
#check HomotopyEquiv.refl
#check HomotopyEquiv.symm
#check HomotopyEquiv.trans
#check HomotopyEquiv.ofIso
#check ConcreteUnboundedContractibleTail
#check addCommGrp_int_not_isZero
#check moduleCat_int_not_isZero
#check AddCommGrpConcreteTailConstructor
#check ModuleCatIntConcreteTailConstructor

end ContractibleTailConcreteScout

end LeanLCAExactChallenge
