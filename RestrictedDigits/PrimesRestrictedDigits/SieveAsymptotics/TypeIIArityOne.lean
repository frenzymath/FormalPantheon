import PrimesRestrictedDigits.SieveAsymptotics.TypeIIRegionGeometry

/-!
# The one-prime Type II region

The convenience condition in Proposition 7.2 forces every one-coordinate source region to be
empty: its fixed subset sum can only be zero or one. This is the branch omitted before the
positive-dimensional cube argument on p. 163 of `MAYNARD-PRD-PUBLISHED`.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- A convenient one-coordinate source region is empty. -/
theorem typeIIRegion_eq_empty_of_arity_one
    {eta epsilon : Real} {region : Set (Fin 1 -> Real)}
    (hepsilon : 0 < epsilon)
    (hregion : IsTypeIISourceRegion eta region)
    (hconvenient : IsTypeIIRegionConvenient epsilon region) :
    region = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty]
  rintro ⟨e, he⟩
  obtain ⟨I, hI⟩ := hconvenient
  have hinterval := hI e he
  by_cases hzero : (0 : Fin 1) ∈ I
  · have hsumI : (∑ i ∈ I, e i) = e 0 := by
      rw [Finset.sum_eq_single 0]
      · intro i hi hine
        exact (hine (Subsingleton.elim i 0)).elim
      · exact fun hnot => (hnot hzero).elim
    have hsum := (hregion he).2.2
    rw [Fin.sum_univ_one] at hsum
    rw [hsumI, hsum] at hinterval
    linarith [hinterval.2]
  · have hIempty : I = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro i hi
      exact hzero (Subsingleton.elim i 0 ▸ hi)
    rw [hIempty] at hinterval
    simp only [Finset.sum_empty] at hinterval
    linarith [hinterval.1]

end

end PrimesRestrictedDigits
