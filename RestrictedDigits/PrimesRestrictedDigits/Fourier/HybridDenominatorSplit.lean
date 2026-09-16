import Mathlib.Data.Nat.GCD.Basic

/-!
# Gcd splitting for the alternative hybrid denominator

The proof of published Lemma 10.7 splits a decimal-smooth denominator using
two nested gcds.  This file proves the exact natural-number identities and the
coprimality premises consumed by the weighted CRT carrier.  No pairwise
coprimality of the three factors is asserted.
-/

namespace PrimesRestrictedDigits

/-! The canonical factors in the order used by the source. -/

def hybridDenominatorThirdFactor (d D : Nat) : Nat := Nat.gcd d D

def hybridDenominatorSecondFactor (d D V : Nat) : Nat :=
  Nat.gcd d (D * V) / hybridDenominatorThirdFactor d D

def hybridDenominatorFirstFactor (d D V : Nat) : Nat :=
  d / Nat.gcd d (D * V)

private theorem hybridDenominatorThirdFactor_dvd_enlargedGcd
    (d D V : Nat) :
    hybridDenominatorThirdFactor d D ∣ Nat.gcd d (D * V) := by
  exact Nat.gcd_dvd_gcd_of_dvd_right d (Nat.dvd_mul_right D V)

theorem hybridDenominatorThirdFactor_dvd_scale (d D : Nat) :
    hybridDenominatorThirdFactor d D ∣ D := by
  exact Nat.gcd_dvd_right d D

theorem hybridDenominatorSecondThird_eq_gcd (d D V : Nat) :
    hybridDenominatorSecondFactor d D V *
        hybridDenominatorThirdFactor d D = Nat.gcd d (D * V) := by
  exact Nat.div_mul_cancel (hybridDenominatorThirdFactor_dvd_enlargedGcd d D V)

theorem hybridDenominatorSecondThird_dvd_scale (d D V : Nat) :
    hybridDenominatorSecondFactor d D V *
        hybridDenominatorThirdFactor d D ∣ D * V := by
  rw [hybridDenominatorSecondThird_eq_gcd]
  exact Nat.gcd_dvd_right d (D * V)

theorem hybridDenominatorFirstSecondThird_eq (d D V : Nat) :
    hybridDenominatorFirstFactor d D V *
        hybridDenominatorSecondFactor d D V *
          hybridDenominatorThirdFactor d D = d := by
  rw [mul_assoc, hybridDenominatorSecondThird_eq_gcd]
  exact Nat.div_mul_cancel (Nat.gcd_dvd_left d (D * V))

theorem hybridDenominatorFirst_eq_div_secondThird (d D V : Nat) :
    hybridDenominatorFirstFactor d D V =
      d / (hybridDenominatorSecondFactor d D V *
        hybridDenominatorThirdFactor d D) := by
  rw [hybridDenominatorSecondThird_eq_gcd]
  rfl

theorem hybridDenominatorFirstSecond_eq_div_third (d D V : Nat) :
    hybridDenominatorFirstFactor d D V *
        hybridDenominatorSecondFactor d D V =
      d / hybridDenominatorThirdFactor d D := by
  unfold hybridDenominatorFirstFactor hybridDenominatorSecondFactor
  exact Nat.div_mul_div
    (Nat.gcd_dvd_left d (D * V))
    (hybridDenominatorThirdFactor_dvd_enlargedGcd d D V)

theorem hybridDenominatorFirstFactor_pos {d D V : Nat} (hd : 0 < d) :
    0 < hybridDenominatorFirstFactor d D V := by
  apply Nat.div_pos
  · exact Nat.le_of_dvd hd (Nat.gcd_dvd_left d (D * V))
  · exact Nat.gcd_pos_of_pos_left (D * V) hd

theorem hybridDenominatorSecondFactor_pos {d D V : Nat} (hd : 0 < d) :
    0 < hybridDenominatorSecondFactor d D V := by
  apply Nat.div_pos
  · exact Nat.le_of_dvd
      (Nat.gcd_pos_of_pos_left (D * V) hd)
      (hybridDenominatorThirdFactor_dvd_enlargedGcd d D V)
  · exact Nat.gcd_pos_of_pos_left D hd

theorem hybridDenominatorThirdFactor_pos {d D : Nat} (hd : 0 < d) :
    0 < hybridDenominatorThirdFactor d D := by
  exact Nat.gcd_pos_of_pos_left D hd

theorem hybridDenominatorFirstSecond_coprime_div_third
    {d D V : Nat} (hd : 0 < d) :
    (hybridDenominatorFirstFactor d D V *
        hybridDenominatorSecondFactor d D V).Coprime
      (D / hybridDenominatorThirdFactor d D) := by
  rw [hybridDenominatorFirstSecond_eq_div_third]
  unfold hybridDenominatorThirdFactor
  exact Nat.coprime_div_gcd_div_gcd
    (Nat.gcd_pos_of_pos_left D hd)

theorem hybridDenominatorFirst_coprime_enlarged_quotient
    {d D V : Nat} (hd : 0 < d) :
    (hybridDenominatorFirstFactor d D V).Coprime
      ((D * V) /
        (hybridDenominatorSecondFactor d D V *
          hybridDenominatorThirdFactor d D)) := by
  rw [hybridDenominatorSecondThird_eq_gcd]
  unfold hybridDenominatorFirstFactor
  exact Nat.coprime_div_gcd_div_gcd
    (Nat.gcd_pos_of_pos_left (D * V) hd)

private theorem hybridDenominatorFirstSecond_dvd_d
    {d D V : Nat} :
    hybridDenominatorFirstFactor d D V *
        hybridDenominatorSecondFactor d D V ∣ d := by
  refine ⟨hybridDenominatorThirdFactor d D, ?_⟩
  exact (hybridDenominatorFirstSecondThird_eq d D V).symm

private theorem hybridDenominatorFirst_dvd_d
    {d D V : Nat} : hybridDenominatorFirstFactor d D V ∣ d := by
  refine ⟨hybridDenominatorSecondFactor d D V *
      hybridDenominatorThirdFactor d D, ?_⟩
  simpa only [mul_assoc] using
    (hybridDenominatorFirstSecondThird_eq d D V).symm

theorem hybridDenominatorScale_mul_firstSecond_coprime
    {d D V q : Nat} (hqd : q.Coprime d) (hqD : q.Coprime D) :
    (D * (hybridDenominatorFirstFactor d D V *
      hybridDenominatorSecondFactor d D V)).Coprime q := by
  apply (hqD.symm).mul_left
  exact (hqd.coprime_dvd_right (hybridDenominatorFirstSecond_dvd_d)).symm

theorem hybridDenominatorScaleDivThird_mul_coprime
    {d D V q : Nat} (hd : 0 < d) (hqd : q.Coprime d) :
    ((D / hybridDenominatorThirdFactor d D) * q).Coprime
      (hybridDenominatorFirstFactor d D V *
        hybridDenominatorSecondFactor d D V) := by
  exact (hybridDenominatorFirstSecond_coprime_div_third
      (d := d) (D := D) (V := V) hd).symm.mul_left
    (hqd.coprime_dvd_right hybridDenominatorFirstSecond_dvd_d)

theorem hybridDenominatorEnlargedScale_mul_first_coprime
    {d D V q : Nat} (hqd : q.Coprime d) (hqDV : q.Coprime (D * V)) :
    ((D * V) * hybridDenominatorFirstFactor d D V).Coprime q := by
  apply (hqDV.symm).mul_left
  exact (hqd.coprime_dvd_right hybridDenominatorFirst_dvd_d).symm

theorem hybridDenominatorEnlargedQuotient_mul_coprime
    {d D V q : Nat} (hd : 0 < d) (hqd : q.Coprime d) :
    (((D * V) /
      (hybridDenominatorSecondFactor d D V *
        hybridDenominatorThirdFactor d D)) * q).Coprime
      (hybridDenominatorFirstFactor d D V) := by
  exact (hybridDenominatorFirst_coprime_enlarged_quotient
      (d := d) (D := D) (V := V) hd).symm.mul_left
    (hqd.coprime_dvd_right hybridDenominatorFirst_dvd_d)

theorem gcd_hybridDenominatorFactors_scale (d D V : Nat) :
    Nat.gcd
        (hybridDenominatorFirstFactor d D V *
          hybridDenominatorSecondFactor d D V *
            hybridDenominatorThirdFactor d D) D =
      hybridDenominatorThirdFactor d D := by
  rw [hybridDenominatorFirstSecondThird_eq]
  rfl

theorem gcd_hybridDenominatorFactors_enlargedScale (d D V : Nat) :
    Nat.gcd
        (hybridDenominatorFirstFactor d D V *
          hybridDenominatorSecondFactor d D V *
            hybridDenominatorThirdFactor d D) (D * V) =
      hybridDenominatorSecondFactor d D V *
        hybridDenominatorThirdFactor d D := by
  rw [hybridDenominatorFirstSecondThird_eq,
    hybridDenominatorSecondThird_eq_gcd]

end PrimesRestrictedDigits
