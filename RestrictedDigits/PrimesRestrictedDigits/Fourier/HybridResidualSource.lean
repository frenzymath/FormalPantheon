import PrimesRestrictedDigits.Fourier.HybridResidualSampling
import PrimesRestrictedDigits.Fourier.LargeSieveScaleSelection

/-!
# Source Residual Carrier and Fixed-Denominator Prefix

This file records the literal `q_2 ~ Q_2` subcarrier from Maynard's Lemma
10.7 and tracks the decimal loss between its `Q_1` scale and fixed `q_1`
rational spacing. See `MAYNARD-PRD-PUBLISHED`, pp. 184--185.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

theorem natCast_div_ten_lt_iff
    {Q q : Nat} :
    ((Q : Real) / 10 < (q : Real)) ↔ Q < 10 * q := by
  rw [div_lt_iff₀ (by norm_num : (0 : Real) < 10)]
  norm_cast
  omega

/-- The literal `q ~ Q`, `(q,10)=1` subcarrier of the residual family. -/
def hybridResidualFractionSourceCarrier (M Q : Nat) :
    Finset (Nat × Nat) :=
  (hybridResidualFractionCarrier M Q).filter fun x =>
    Q < 10 * x.1 ∧ x.1.Coprime 10

theorem mem_hybridResidualFractionSourceCarrier_iff
    {M Q : Nat} {x : Nat × Nat} :
    x ∈ hybridResidualFractionSourceCarrier M Q ↔
      1 <= x.1 ∧ x.1 <= Q ∧ Q < 10 * x.1 ∧
        x.1.Coprime 10 ∧ x.2 < M * x.1 ∧
        x.2.Coprime (M * x.1) := by
  rw [hybridResidualFractionSourceCarrier, Finset.mem_filter,
    mem_hybridResidualFractionCarrier_iff]
  aesop

theorem sum_hybridResidualFractionSourceCarrier_le
    (digit : Fin 10) (length M Q : Nat) (hM : 0 < M) (hQ : 0 < Q)
    {delta K : Real} (hdelta : 0 <= delta)
    (hscale : 10 ^ length <= M * Q ^ 2)
    (hdensity : delta * ((10 ^ length : Nat) : Real) <= K) :
    (∑ x ∈ hybridResidualFractionSourceCarrier M Q,
      closedWindowMaximum
        (normalizedPaddedDigitFourierMagnitudeSqAt digit length) delta
        (hybridResidualFractionValue M x)) <=
      36 * (1 + 2 * K) * ((M : Real) * (Q : Real) ^ 2) /
        (9 : Real) ^ length := by
  let value (x : Nat × Nat) :=
    closedWindowMaximum
      (normalizedPaddedDigitFourierMagnitudeSqAt digit length) delta
      (hybridResidualFractionValue M x)
  have hsubset :
      hybridResidualFractionSourceCarrier M Q <=
        hybridResidualFractionCarrier M Q := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hnonneg (x : Nat × Nat) : 0 <= value x := by
    dsimp [value]
    apply closedWindowMaximum_nonneg
    · exact normalizedPaddedDigitFourierMagnitudeSqAt_continuous digit length
    · intro z
      rw [normalizedPaddedDigitFourierMagnitudeSqAt_eq_magnitude_sq]
      positivity
    · exact hdelta
  calc
    (∑ x ∈ hybridResidualFractionSourceCarrier M Q, value x) <=
        ∑ x ∈ hybridResidualFractionCarrier M Q, value x := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun x hx hsource => hnonneg x)
    _ <= 36 * (1 + 2 * K) * ((M : Real) * (Q : Real) ^ 2) /
        (9 : Real) ^ length := by
      simpa only [value] using sum_hybridResidualFractionCarrier_le
        digit length M Q hM hQ hdelta hscale hdensity

theorem exists_hybridResidualSourceDecimalPrefix
    {d q Q1 Q2 v : Nat} (hd : 0 < d) (hq : 0 < q) (hQ2 : 0 < Q2)
    (hqLower : Q1 < 10 * q) (hqUpper : q <= Q1) :
    ∃ r : Nat,
      r <= v ∧
        10 ^ r <= d * q * Q2 ^ 2 ∧
        d * q * Q2 ^ 2 <= d * Q1 * Q2 ^ 2 ∧
        min (10 ^ v) (d * Q1 * Q2 ^ 2) < 100 * 10 ^ r := by
  let L : Real := ((d * q * Q2 ^ 2 : Nat) : Real)
  have hL : (1 : Real) <= L := by
    dsimp [L]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero hd.ne' hq.ne') (pow_ne_zero 2 hQ2.ne'))
  obtain ⟨r, hrv, hrL, hrV, hclose, hfull⟩ :=
    exists_largeSieve_decimalPrefix hL v
  refine ⟨r, hrv, ?_, ?_, ?_⟩
  · dsimp [L] at hrL
    exact_mod_cast hrL
  · exact Nat.mul_le_mul_right (Q2 ^ 2)
      (Nat.mul_le_mul_left d hqUpper)
  · have hsourceScale :
        d * Q1 * Q2 ^ 2 < 10 * (d * q * Q2 ^ 2) := by
      have hfirst : d * Q1 < d * (10 * q) :=
        Nat.mul_lt_mul_of_pos_left hqLower hd
      have hsecond : d * Q1 * Q2 ^ 2 < d * (10 * q) * Q2 ^ 2 :=
        Nat.mul_lt_mul_of_pos_right hfirst (pow_pos hQ2 2)
      simpa [mul_comm, mul_left_comm, mul_assoc] using hsecond
    have hsourceScaleReal :
        ((d * Q1 * Q2 ^ 2 : Nat) : Real) < 10 * L := by
      dsimp [L]
      exact_mod_cast hsourceScale
    have hclose' :
        min L (((10 ^ v : Nat) : Real)) <
          10 * ((10 ^ r : Nat) : Real) := by
      simpa [L] using hclose
    have hresultReal :
        min (((10 ^ v : Nat) : Real))
            ((d * Q1 * Q2 ^ 2 : Nat) : Real) <
          100 * ((10 ^ r : Nat) : Real) := by
      by_cases hVL : ((10 ^ v : Nat) : Real) <= L
      · have hminVL : min L (((10 ^ v : Nat) : Real)) =
            ((10 ^ v : Nat) : Real) := min_eq_right hVL
        calc
          min (((10 ^ v : Nat) : Real))
              ((d * Q1 * Q2 ^ 2 : Nat) : Real) <=
              ((10 ^ v : Nat) : Real) := min_le_left _ _
          _ = min L (((10 ^ v : Nat) : Real)) := hminVL.symm
          _ < 10 * ((10 ^ r : Nat) : Real) := hclose'
          _ < 100 * ((10 ^ r : Nat) : Real) := by
            have hR : (0 : Real) < (10 ^ r : Nat) := by positivity
            nlinarith
      · have hLV : L < ((10 ^ v : Nat) : Real) := lt_of_not_ge hVL
        have hminVL : min L (((10 ^ v : Nat) : Real)) = L :=
          min_eq_left hLV.le
        calc
          min (((10 ^ v : Nat) : Real))
              ((d * Q1 * Q2 ^ 2 : Nat) : Real) <=
              ((d * Q1 * Q2 ^ 2 : Nat) : Real) := min_le_right _ _
          _ < 10 * L := hsourceScaleReal
          _ = 10 * min L (((10 ^ v : Nat) : Real)) := by rw [hminVL]
          _ < 10 * (10 * ((10 ^ r : Nat) : Real)) := by
            exact mul_lt_mul_of_pos_left hclose' (by norm_num)
          _ = 100 * ((10 ^ r : Nat) : Real) := by ring
    have hresultCast :
        ((min (10 ^ v) (d * Q1 * Q2 ^ 2) : Nat) : Real) <
          ((100 * 10 ^ r : Nat) : Real) := by
      simpa only [Nat.cast_min, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
        using hresultReal
    exact_mod_cast hresultCast

end

end PrimesRestrictedDigits
