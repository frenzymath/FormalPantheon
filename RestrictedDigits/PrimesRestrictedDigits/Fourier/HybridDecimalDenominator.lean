import PrimesRestrictedDigits.Fourier.HybridDenominatorSplit

/-!
# Decimal-power specialization of the hybrid denominator split

This file lifts coprimality with ten to the exact power-of-ten hypotheses used
by the weighted CRT maps in published Lemma 10.7.  The nested gcd algebra is
proved in `HybridDenominatorSplit.lean`.
-/

namespace PrimesRestrictedDigits

theorem coprime_dvd_pow_ten {q d u : Nat} (hq : q.Coprime 10)
    (hdvd : d ∣ 10 ^ u) : q.Coprime d := by
  exact (hq.pow_right u).coprime_dvd_right hdvd

theorem decimalHybridScale_mul_firstSecond_coprime
    {q d k v u : Nat} (hdvd : d ∣ 10 ^ u)
    (hq10 : q.Coprime 10) :
    (10 ^ k *
      (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v) *
        hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))).Coprime q := by
  exact hybridDenominatorScale_mul_firstSecond_coprime
    (d := d) (D := 10 ^ k) (V := 10 ^ v) (q := q)
    (coprime_dvd_pow_ten hq10 hdvd) (hq10.pow_right k)

theorem decimalHybridScaleDivThird_mul_coprime
    {q d k v u : Nat} (hd : 0 < d) (hdvd : d ∣ 10 ^ u)
    (hq10 : q.Coprime 10) :
    ((10 ^ k / hybridDenominatorThirdFactor d (10 ^ k)) * q).Coprime
      (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v) *
        hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)) := by
  exact hybridDenominatorScaleDivThird_mul_coprime
    (d := d) (D := 10 ^ k) (V := 10 ^ v) (q := q) hd
    (coprime_dvd_pow_ten hq10 hdvd)

theorem decimalHybridEnlargedScale_mul_first_coprime
    {q d k v u : Nat} (hdvd : d ∣ 10 ^ u)
    (hq10 : q.Coprime 10) :
    ((10 ^ k * 10 ^ v) * hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)).Coprime q := by
  exact hybridDenominatorEnlargedScale_mul_first_coprime
    (d := d) (D := 10 ^ k) (V := 10 ^ v) (q := q)
    (coprime_dvd_pow_ten hq10 hdvd)
    ((hq10.pow_right k).mul_right (hq10.pow_right v))

theorem decimalHybridEnlargedQuotient_mul_coprime
    {q d k v u : Nat} (hd : 0 < d) (hdvd : d ∣ 10 ^ u)
    (hq10 : q.Coprime 10) :
    (((10 ^ k * 10 ^ v) /
      (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v) *
        hybridDenominatorThirdFactor d (10 ^ k))) * q).Coprime
      (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)) := by
  exact hybridDenominatorEnlargedQuotient_mul_coprime
    (d := d) (D := 10 ^ k) (V := 10 ^ v) (q := q) hd
    (coprime_dvd_pow_ten hq10 hdvd)

end PrimesRestrictedDigits
