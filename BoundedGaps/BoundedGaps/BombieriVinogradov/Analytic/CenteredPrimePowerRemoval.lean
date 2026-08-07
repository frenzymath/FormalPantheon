import BoundedGaps.BombieriVinogradov.Analytic.CenteredProgressionCorrection

/-!
# Centered prime-power removal

This file passes from the globally Chebyshev-psi-centered progression sum to
the corresponding theta-weighted progression sum. The progression and global
prime-power remainders both lie in the interval from zero to `psi - theta`, so
their centered difference costs one copy of that global remainder rather than
two.

The inclusive progression functions follow `AkbaryHambrook2013v2`, printed
p. 4. The global prime-power estimate is classical; see
`KoukoulopoulosDistributionPrimesPrelim2022`, Exercise 2.7, printed p. 33.
The centered comparison and natural-endpoint maximum are project-derived.
Semantic review: `SEM-572`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators ArithmeticFunction.vonMangoldt

noncomputable section

/-- The logarithmically weighted sum of primes up to `x` in one natural
remainder class modulo `q`. -/
noncomputable def thetaProgressionSum (x q a : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE x with p % q = a % q, Real.log (p : ℝ)

/-- The non-prime von Mangoldt contribution in one progression. Since von
Mangoldt vanishes off prime powers, this is the square-and-higher remainder. -/
noncomputable def progressionPrimePowerRemainder (x q a : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 x with n % q = a % q ∧ ¬n.Prime,
    ArithmeticFunction.vonMangoldt n

/-- The signed theta-weighted progression error with global theta center. -/
noncomputable def centeredThetaProgressionError (x q a : ℕ) : ℝ :=
  thetaProgressionSum x q a -
    Chebyshev.theta (x : ℝ) / (q.totient : ℝ)

/-- The absolute globally theta-centered progression discrepancy. -/
noncomputable def centeredThetaProgressionDiscrepancy (x q a : ℕ) : ℝ :=
  |centeredThetaProgressionError x q a|

/-- Reduced-residue maximum of the globally theta-centered discrepancy. -/
noncomputable def maxCenteredThetaProgressionDiscrepancy
    (x q : ℕ) : ℝ :=
  if hq : 0 < q then
    (coprimeResidues q).sup' (coprimeResidues_nonempty hq)
      (centeredThetaProgressionDiscrepancy x q)
  else 0

/-- Endpoint-outer, reduced-residue-inner theta discrepancy maximum. -/
noncomputable def maxCenteredThetaProgressionDiscrepancyUpTo
    (x q : ℕ) : ℝ :=
  if hx : 2 ≤ x then
    (Finset.Icc 2 x).sup' (weightedEndpointRange_nonempty hx)
      (fun y ↦ maxCenteredThetaProgressionDiscrepancy y q)
  else 0

/-- Split the progression von Mangoldt sum into its prime and higher-prime-
power parts. -/
theorem chebyshevProgressionSum_eq_thetaProgressionSum_add_remainder
    (x q a : ℕ) :
    chebyshevProgressionSum x q a =
      thetaProgressionSum x q a + progressionPrimePowerRemainder x q a := by
  classical
  rw [chebyshevProgressionSum]
  rw [← Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 1 x).filter (fun n ↦ n % q = a % q)) Nat.Prime]
  congr 1
  · rw [thetaProgressionSum, Nat.primesLE_eq_filter_Icc_one,
      Finset.filter_comm]
    apply Finset.sum_congr rfl
    intro p hp
    rw [ArithmeticFunction.vonMangoldt_apply_prime]
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  · simp only [progressionPrimePowerRemainder, Finset.filter_filter]

/-- The progression prime-power remainder is nonnegative. -/
theorem progressionPrimePowerRemainder_nonneg (x q a : ℕ) :
    0 ≤ progressionPrimePowerRemainder x q a := by
  apply Finset.sum_nonneg
  intro n _hn
  exact ArithmeticFunction.vonMangoldt_nonneg

/-- A progression prime-power remainder is at most the global remainder. -/
theorem progressionPrimePowerRemainder_le_psi_sub_theta (x q a : ℕ) :
    progressionPrimePowerRemainder x q a ≤
      Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ) := by
  rw [progressionPrimePowerRemainder,
    Chebyshev.psi_sub_theta_eq_sum_not_prime]
  simp only [Nat.floor_natCast]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnIcc, _hnMod, hnPrime⟩
    have hnBounds := Finset.mem_Icc.mp hnIcc
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨by omega, hnBounds.2⟩, hnPrime⟩
  · intro n _hn _hn'
    exact ArithmeticFunction.vonMangoldt_nonneg

/-- The global prime-power remainder is monotone at natural endpoints. -/
theorem monotone_natCast_psi_sub_theta :
    Monotone (fun x : ℕ ↦
      Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ)) := by
  intro x y hxy
  change Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ) ≤
    Chebyshev.psi (y : ℝ) - Chebyshev.theta (y : ℝ)
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime,
    Chebyshev.psi_sub_theta_eq_sum_not_prime]
  simp only [Nat.floor_natCast]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnIoc, hnPrime⟩
    have hnBounds := Finset.mem_Ioc.mp hnIoc
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨hnBounds.1, hnBounds.2.trans hxy⟩, hnPrime⟩
  · intro n _hn _hn'
    exact ArithmeticFunction.vonMangoldt_nonneg

/-- Removing prime powers from both the progression and its global center
costs one copy of the global prime-power remainder. -/
theorem centeredThetaProgressionDiscrepancy_le
    {x q a : ℕ} (hq : 1 ≤ q) :
    centeredThetaProgressionDiscrepancy x q a ≤
      centeredProgressionDiscrepancy x q a +
        (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ)) := by
  let P := progressionPrimePowerRemainder x q a
  let R := Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ)
  have hP0 : 0 ≤ P := by
    simpa only [P] using progressionPrimePowerRemainder_nonneg x q a
  have hPR : P ≤ R := by
    simpa only [P, R] using
      progressionPrimePowerRemainder_le_psi_sub_theta x q a
  have hR0 : 0 ≤ R := by
    simpa only [R] using sub_nonneg.mpr (Chebyshev.theta_le_psi (x : ℝ))
  have hphi : (1 : ℝ) ≤ (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
  have hRdiv0 : 0 ≤ R / (q.totient : ℝ) :=
    div_nonneg hR0 (by positivity)
  have hRdivR : R / (q.totient : ℝ) ≤ R :=
    div_le_self hR0 hphi
  have hcorrection : |R / (q.totient : ℝ) - P| ≤ R := by
    rw [abs_le]
    constructor <;> linarith
  have htheta :
      thetaProgressionSum x q a = chebyshevProgressionSum x q a - P := by
    have hsplit :=
      chebyshevProgressionSum_eq_thetaProgressionSum_add_remainder x q a
    dsimp only [P]
    linarith
  have hcenter :
      centeredThetaProgressionError x q a =
        (chebyshevProgressionSum x q a -
            Chebyshev.psi (x : ℝ) / (q.totient : ℝ)) +
          (R / (q.totient : ℝ) - P) := by
    rw [centeredThetaProgressionError, htheta]
    dsimp only [R]
    ring
  rw [centeredThetaProgressionDiscrepancy, hcenter,
    centeredProgressionDiscrepancy]
  exact (abs_add_le _ _).trans (add_le_add le_rfl hcorrection)

/-- Unfold the totalized theta maximum on its positive source range. -/
theorem
    maxCenteredThetaProgressionDiscrepancyUpTo_eq_sup_endpoint_residues
    {x q : ℕ} (hx : 2 ≤ x) (hq : 0 < q) :
    maxCenteredThetaProgressionDiscrepancyUpTo x q =
      (Finset.Icc 2 x).sup' (weightedEndpointRange_nonempty hx) (fun y ↦
        (coprimeResidues q).sup' (coprimeResidues_nonempty hq) (fun a ↦
          |thetaProgressionSum y q a -
            Chebyshev.theta (y : ℝ) / (q.totient : ℝ)|)) := by
  rw [maxCenteredThetaProgressionDiscrepancyUpTo, dif_pos hx]
  simp_rw [maxCenteredThetaProgressionDiscrepancy, dif_pos hq,
    centeredThetaProgressionDiscrepancy, centeredThetaProgressionError]

/-- The endpoint theta maximum costs one global prime-power remainder beyond
the endpoint psi maximum. -/
theorem maxCenteredThetaProgressionDiscrepancyUpTo_le
    {x q : ℕ} (hq : 1 ≤ q) :
    maxCenteredThetaProgressionDiscrepancyUpTo x q ≤
      maxCenteredProgressionDiscrepancyUpTo x q +
        (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ)) := by
  by_cases hx : 2 ≤ x
  · have hqpos : 0 < q := by omega
    rw [maxCenteredThetaProgressionDiscrepancyUpTo_eq_sup_endpoint_residues
      hx hqpos]
    apply Finset.sup'_le
    intro y hy
    apply Finset.sup'_le
    intro a ha
    have hpoint := centeredThetaProgressionDiscrepancy_le
      (x := y) (q := q) (a := a) hq
    have hpsi :
        centeredProgressionDiscrepancy y q a ≤
          maxCenteredProgressionDiscrepancyUpTo x q := by
      rw [maxCenteredProgressionDiscrepancyUpTo_eq_sup_endpoint_residues
        hx hqpos]
      exact Finset.le_sup'_of_le
        (fun z ↦
          (coprimeResidues q).sup' (coprimeResidues_nonempty hqpos)
            (fun b ↦ centeredProgressionDiscrepancy z q b)) hy
        (Finset.le_sup'_of_le (centeredProgressionDiscrepancy y q) ha le_rfl)
    have hrem := monotone_natCast_psi_sub_theta (Finset.mem_Icc.mp hy).2
    simpa only [centeredThetaProgressionDiscrepancy,
      centeredThetaProgressionError] using
      hpoint.trans (add_le_add hpsi hrem)
  · have hxReal : (x : ℝ) < 2 := by
      exact_mod_cast Nat.lt_of_not_ge hx
    simp [maxCenteredThetaProgressionDiscrepancyUpTo,
      maxCenteredProgressionDiscrepancyUpTo, hx,
      Chebyshev.psi_eq_zero_of_lt_two hxReal,
      Chebyshev.theta_eq_zero_of_lt_two hxReal]

/-- Summed prime-power removal adds the displayed uniform `Q` copies of the
global remainder. -/
theorem sum_maxCenteredThetaProgressionDiscrepancyUpTo_le (x Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q,
      maxCenteredThetaProgressionDiscrepancyUpTo x q) ≤
      (∑ q ∈ Finset.Icc 1 Q,
        maxCenteredProgressionDiscrepancyUpTo x q) +
        (Q : ℝ) *
          (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ)) := by
  calc
    (∑ q ∈ Finset.Icc 1 Q,
        maxCenteredThetaProgressionDiscrepancyUpTo x q) ≤
        ∑ q ∈ Finset.Icc 1 Q,
          (maxCenteredProgressionDiscrepancyUpTo x q +
            (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ))) := by
      apply Finset.sum_le_sum
      intro q hq
      exact maxCenteredThetaProgressionDiscrepancyUpTo_le
        (Finset.mem_Icc.mp hq).1
    _ = (∑ q ∈ Finset.Icc 1 Q,
          maxCenteredProgressionDiscrepancyUpTo x q) +
        (Q : ℝ) *
          (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ)) := by
      rw [Finset.sum_add_distrib]
      simp [nsmul_eq_mul]
      ring

end

end BoundedGaps.Maynard
