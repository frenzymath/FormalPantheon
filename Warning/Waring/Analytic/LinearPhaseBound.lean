import Waring.Analytic.DiophantineMinimumSum

/-!
# A zero-safe linear phase bound

This file connects the interval Fourier-coefficient estimate to the
zero-safe Diophantine weight used in Chen's Lemma 9.
-/

namespace Waring.Analytic

/-- An interval no longer than `P` is bounded by the zero-safe reciprocal
least-residue weight. -/
theorem norm_intervalFourierCoefficient_le_diophantineMinWeight
    {q : Nat} [NeZero q] (M : Int) (m P : Nat) (hm : m ≤ P)
    (h : ZMod q) :
    ‖intervalFourierCoefficient M m h‖ ≤
      diophantineMinWeight q P h := by
  by_cases hh : h = 0
  · rw [diophantineMinWeight, if_pos hh]
    exact (norm_intervalFourierCoefficient_le_length M m h).trans
      (by exact_mod_cast hm)
  · rw [diophantineMinWeight, if_neg hh]
    exact (norm_intervalFourierCoefficient_le_min_length_leastResidue
      M m hh).trans (min_le_min (by exact_mod_cast hm) le_rfl)

end Waring.Analytic
