import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Algebra.Group.GroupTopology
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.CategoryTheory.Abelian.Basic

/-!
This file is intentionally small. It anchors the current mathlib names that are
likely relevant to the challenge goal, so the worker can start from checked
imports rather than from memory.
-/

namespace LeanLCAExactChallenge

open CategoryTheory

#check TopCat
#check TopCat.Hom
#check AddGroupTopology
#check LocallyCompactSpace
#check MetricSpace
#check AddCommGrpCat
#check AddCommGrpCat.Hom
#check ShortComplex
#check ShortComplex.Exact
#check DerivedCategory
#check HasDerivedCategory
#check Abelian.Ext
#check Abelian
#check Preadditive
#check Limits.HasKernel
#check Limits.HasCokernel

end LeanLCAExactChallenge
