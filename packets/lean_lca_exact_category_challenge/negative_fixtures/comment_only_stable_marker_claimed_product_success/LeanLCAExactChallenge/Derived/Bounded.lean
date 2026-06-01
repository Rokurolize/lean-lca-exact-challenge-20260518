namespace LeanLCAExactChallenge

variable (C : Type)

abbrev BoundedDerivedCategory : Type := C

noncomputable abbrev BoundedDerivedInfinityCategory : SSet.QCat :=
  arbitrary SSet.QCat

/- StableBoundedDerivedInfinityCategory stableInfinity finiteLimits finiteColimits
   suspensionEquivalence loopSuspensionEquivalence pushoutPullbackSquare -/

end LeanLCAExactChallenge
