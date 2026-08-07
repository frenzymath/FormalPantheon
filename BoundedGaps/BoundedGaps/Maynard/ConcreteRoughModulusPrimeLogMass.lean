import BoundedGaps.Maynard.RoughModulusPrimeLogMass

noncomputable section

/-!
# Logarithmic threshold for the varying S2 modulus

Choosing the natural threshold `floor (log R)` turns the rough-modulus
prime-log mass into the `O(log log R)` parameter used in Maynard2013v3,
source line 526.
-/

namespace BoundedGaps.Maynard

open Finset Nat Real

theorem exists_uniform_primeLogDivisorMass_le_log_log_add :
    ∃ C : ℝ, ∀ {P R : ℕ}, 0 < P → Squarefree P → P < R →
      2 ≤ Real.log R →
      primeLogDivisorMass P ≤ Real.log (Real.log R) + C + 2 := by
  obtain ⟨C, hmass⟩ := exists_uniform_primeLogDivisorMass_bound
  refine ⟨C, fun {P R} hP hPsq hPR hlogR => ?_⟩
  let T := ⌊Real.log R⌋₊
  have hlogRPos : 0 < Real.log R := by linarith
  have hT : 0 < T := by
    exact Nat.floor_pos.mpr (by linarith)
  have hfloorLe : (T : ℝ) ≤ Real.log R := by
    exact Nat.floor_le hlogRPos.le
  have hfloorHalf : Real.log R / 2 ≤ (T : ℝ) := by
    have hsub : Real.log R / 2 ≤ Real.log R - 1 := by linarith
    exact hsub.trans (Nat.sub_one_lt_floor (Real.log R)).le
  have hfloorPos : (0 : ℝ) < T := by exact_mod_cast hT
  have hlogFloor : Real.log T ≤ Real.log (Real.log R) := by
    exact Real.strictMonoOn_log.monotoneOn hfloorPos hlogRPos hfloorLe
  have hlogP : Real.log P ≤ Real.log R := by
    exact Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; exact_mod_cast hP)
      (by simp only [Set.mem_Ioi]; exact_mod_cast hP.trans hPR)
      (by exact_mod_cast hPR.le)
  have hratio : Real.log P / T ≤ 2 := by
    rw [div_le_iff₀ hfloorPos]
    linarith
  have hbase := hmass (P := P) (T := T) hPsq hT
  linarith

theorem exists_uniform_augmentedPreSievedPrimeLogInterval_logarithmic_bounds :
    ∃ K C : ℝ, 0 < K ∧
      ∀ {D P R w z : ℕ}, 0 < P → Squarefree P → P < R →
        2 ≤ Real.log R → 2 ≤ w → w ≤ z →
        -(K + Real.log D + (Real.log (Real.log R) + C + 2)) ≤
          augmentedPreSievedPrimeLogIntervalSum D P w z -
            Real.log ((z : ℝ) / (w : ℝ)) ∧
        augmentedPreSievedPrimeLogIntervalSum D P w z -
            Real.log ((z : ℝ) / (w : ℝ)) ≤ K := by
  obtain ⟨K, hK, hinterval⟩ :=
    exists_uniform_augmentedPreSievedPrimeLogInterval_bounds
  obtain ⟨C, hmass⟩ :=
    exists_uniform_primeLogDivisorMass_le_log_log_add
  refine ⟨K, C, hK, fun {D P R w z} hP hPsq hPR hlogR hw hwz => ?_⟩
  have hbounds := hinterval (D := D) (P := P) hP hw hwz
  have hmassBound := hmass hP hPsq hPR hlogR
  constructor
  · linarith [hbounds.1]
  · exact hbounds.2

end BoundedGaps.Maynard
