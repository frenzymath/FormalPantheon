import PrimesRestrictedDigits.SieveAsymptotics.TypeIIAffineHalfspaces

/-!
# Zero projected normals for Type II affine slabs

Canonical sum-one completion makes a full affine form constant exactly when all of its
coefficients agree. This file classifies that degenerate case before the nonzero projected
normals are sent to slab counting.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The pullback, through canonical sum-one completion, of an absolute affine
slab in the full coordinate space. -/
def typeIIProjectedAffineSlab {k : Nat}
    (normal : Fin (k + 1) -> Real) (bound gamma : Real) :
    Set (Fin k -> Real) :=
  {x | |typeIIAffineValue normal (completeProjectedLogTuple x) - bound| <=
    gamma}

/-- A projected normal vanishes exactly when every prefix coefficient agrees
with the coefficient of the completed last coordinate. -/
theorem typeIIProjectedAffineNormal_eq_zero_iff
    {k : Nat} (normal : Fin (k + 1) -> Real) :
    typeIIProjectedAffineNormal normal = 0 ↔
      ∀ i : Fin k, normal i.castSucc = normal (Fin.last k) := by
  constructor
  · intro hzero i
    have hi := congrFun hzero i
    simpa [typeIIProjectedAffineNormal] using sub_eq_zero.mp hi
  · intro hcoeff
    funext i
    simp [typeIIProjectedAffineNormal, hcoeff i]

/-- A projected normal is nonzero exactly when some prefix coefficient differs
from the coefficient of the completed last coordinate. -/
theorem typeIIProjectedAffineNormal_ne_zero_iff
    {k : Nat} (normal : Fin (k + 1) -> Real) :
    typeIIProjectedAffineNormal normal ≠ 0 ↔
      ∃ i : Fin k, normal i.castSucc ≠ normal (Fin.last k) := by
  classical
  simpa only [ne_eq, not_forall] using
    not_congr (typeIIProjectedAffineNormal_eq_zero_iff normal)

/-- Under a zero projected normal, slab membership is the scalar condition on
the constant value of the completed affine form. -/
theorem mem_typeIIProjectedAffineSlab_iff_of_projected_eq_zero
    {k : Nat} {normal : Fin (k + 1) -> Real} {bound gamma : Real}
    {x : Fin k -> Real} (hzero : typeIIProjectedAffineNormal normal = 0) :
    x ∈ typeIIProjectedAffineSlab normal bound gamma ↔
      |normal (Fin.last k) - bound| <= gamma := by
  change |typeIIAffineValue normal (completeProjectedLogTuple x) - bound| <=
      gamma ↔ _
  rw [typeIIAffineValue_completeProjectedLogTuple, hzero]
  simp [typeIIAffineValue]

/-- A zero-projected affine slab is exactly all points or no points according
to its scalar constant-value condition. -/
theorem typeIIProjectedAffineSlab_eq_ite_of_projected_eq_zero
    {k : Nat} {normal : Fin (k + 1) -> Real} {bound gamma : Real}
    (hzero : typeIIProjectedAffineNormal normal = 0) :
    typeIIProjectedAffineSlab normal bound gamma =
      if |normal (Fin.last k) - bound| <= gamma then Set.univ else ∅ := by
  ext x
  rw [mem_typeIIProjectedAffineSlab_iff_of_projected_eq_zero hzero]
  by_cases hscalar : |normal (Fin.last k) - bound| <= gamma <;>
    simp [hscalar]

/-- The true scalar branch of a zero-projected affine slab is the whole
projected space. -/
theorem typeIIProjectedAffineSlab_eq_univ_of_projected_eq_zero
    {k : Nat} {normal : Fin (k + 1) -> Real} {bound gamma : Real}
    (hzero : typeIIProjectedAffineNormal normal = 0)
    (hscalar : |normal (Fin.last k) - bound| <= gamma) :
    typeIIProjectedAffineSlab normal bound gamma = Set.univ := by
  rw [typeIIProjectedAffineSlab_eq_ite_of_projected_eq_zero hzero]
  simp [hscalar]

/-- The false scalar branch of a zero-projected affine slab is empty. -/
theorem typeIIProjectedAffineSlab_eq_empty_of_projected_eq_zero
    {k : Nat} {normal : Fin (k + 1) -> Real} {bound gamma : Real}
    (hzero : typeIIProjectedAffineNormal normal = 0)
    (hscalar : ¬ (|normal (Fin.last k) - bound| <= gamma)) :
    typeIIProjectedAffineSlab normal bound gamma = ∅ := by
  rw [typeIIProjectedAffineSlab_eq_ite_of_projected_eq_zero hzero]
  simp [hscalar]

/-- If the completed coordinate is absent from the full affine form, any
nonzero prefix coefficient gives a genuinely nonzero projected normal. -/
theorem typeIIProjectedAffineNormal_ne_zero_of_last_eq_zero
    {k : Nat} {normal : Fin (k + 1) -> Real}
    (hlast : normal (Fin.last k) = 0)
    (hprefix : ∃ i : Fin k, normal i.castSucc ≠ 0) :
    typeIIProjectedAffineNormal normal ≠ 0 := by
  rw [typeIIProjectedAffineNormal_ne_zero_iff]
  obtain ⟨i, hi⟩ := hprefix
  exact ⟨i, by simpa [hlast] using hi⟩

end

end PrimesRestrictedDigits
