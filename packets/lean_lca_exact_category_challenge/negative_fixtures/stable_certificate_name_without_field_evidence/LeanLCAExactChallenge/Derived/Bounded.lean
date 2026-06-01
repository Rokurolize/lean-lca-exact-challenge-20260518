namespace LeanLCAExactChallenge

variable (C : Type)

abbrev BoundedDerivedCategory : Type := C

noncomputable abbrev BoundedDerivedInfinityCategory : SSet.QCat :=
  arbitrary SSet.QCat

noncomputable abbrev StableBoundedDerivedInfinityCategory : SSet.QCat :=
  BoundedDerivedInfinityCategory C

end LeanLCAExactChallenge
