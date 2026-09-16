import PrimesRestrictedDigits.Fourier.SquaredTransformTwoScaleSampling
import PrimesRestrictedDigits.Fourier.RationalCircleSpacing
import Mathlib.Order.Interval.Finset.Nat

/-!
# Residual reduced-fraction sampling

This module supplies the canonical rational carrier and exact squared-transform sampler used
for the residual sums in published Lemma 10.7.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-- Reduced fractions with denominator `M * q` for `1 <= q <= Q`. -/
def hybridResidualFractionCarrier (M Q : Nat) : Finset (Nat × Nat) :=
  ((Finset.Icc 1 Q).product (Finset.range (M * Q))).filter fun x =>
    x.2 < M * x.1 ∧ x.2.Coprime (M * x.1)

theorem mem_hybridResidualFractionCarrier_iff
    {M Q : Nat} {x : Nat × Nat} :
    x ∈ hybridResidualFractionCarrier M Q ↔
      1 ≤ x.1 ∧ x.1 ≤ Q ∧ x.2 < M * x.1 ∧
        x.2.Coprime (M * x.1) := by
  constructor
  · intro hx
    rcases Finset.mem_filter.mp hx with ⟨hprod, hdata⟩
    rcases Finset.mem_product.mp hprod with ⟨hq, ha⟩
    exact ⟨(Finset.mem_Icc.mp hq).1, (Finset.mem_Icc.mp hq).2,
      hdata.1, hdata.2⟩
  · rintro ⟨hq1, hqQ, ha, hcop⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hq1, hqQ⟩, ?_⟩,
      ha, hcop⟩
    exact Finset.mem_range.mpr
      (ha.trans_le (Nat.mul_le_mul_left M hqQ))

private def hybridResidualFractionRat (M : Nat) (x : Nat × Nat) : Rat :=
  (x.2 : Rat) / ((M * x.1 : Nat) : Rat)

/-- The real point represented by a residual-fraction carrier pair. -/
noncomputable def hybridResidualFractionValue
    (M : Nat) (x : Nat × Nat) : Real :=
  (x.2 : Real) / ((M * x.1 : Nat) : Real)

private theorem intNatAbs_coprime_of_natCoprime_residual
    {a q : Nat} (hcoprime : a.Coprime q) :
    (a : Int).natAbs.Coprime (q : Int).natAbs := by
  simpa using hcoprime

private theorem hybridResidualFractionRat_den_eq
    {M Q : Nat} (hM : 0 < M) {x : Nat × Nat}
    (hx : x ∈ hybridResidualFractionCarrier M Q) :
    (hybridResidualFractionRat M x).den = M * x.1 := by
  have hdata := mem_hybridResidualFractionCarrier_iff.mp hx
  have hq : 0 < x.1 := lt_of_lt_of_le Nat.zero_lt_one hdata.1
  have hden := Rat.den_div_eq_of_coprime
    (a := (x.2 : Int)) (b := (M * x.1 : Int))
    (by exact_mod_cast Nat.mul_pos hM hq : (0 : Int) < (M * x.1 : Int))
    (intNatAbs_coprime_of_natCoprime_residual hdata.2.2.2)
  have hcast : hybridResidualFractionRat M x =
      ((x.2 : Int) : Rat) / ((M * x.1 : Int) : Rat) := by
    norm_num [hybridResidualFractionRat]
  calc
    (hybridResidualFractionRat M x).den =
        ((((x.2 : Int) : Rat) / ((M * x.1 : Int) : Rat))).den :=
      congrArg Rat.den hcast
    _ = M * x.1 := by exact_mod_cast hden

private theorem hybridResidualFractionRat_nonneg
    {M Q : Nat} (hM : 0 < M) {x : Nat × Nat}
    (hx : x ∈ hybridResidualFractionCarrier M Q) :
    0 ≤ hybridResidualFractionRat M x := by
  have hdata := mem_hybridResidualFractionCarrier_iff.mp hx
  have hq : 0 < x.1 := lt_of_lt_of_le Nat.zero_lt_one hdata.1
  change (0 : Rat) ≤ (x.2 : Rat) / ((M * x.1 : Nat) : Rat)
  positivity

private theorem hybridResidualFractionRat_lt_one
    {M Q : Nat} (hM : 0 < M) {x : Nat × Nat}
    (hx : x ∈ hybridResidualFractionCarrier M Q) :
    hybridResidualFractionRat M x < 1 := by
  have hdata := mem_hybridResidualFractionCarrier_iff.mp hx
  have hq : 0 < x.1 := lt_of_lt_of_le Nat.zero_lt_one hdata.1
  have hden : (0 : Rat) < (M * x.1 : Nat) := by
    exact_mod_cast Nat.mul_pos hM hq
  change (x.2 : Rat) / ((M * x.1 : Nat) : Rat) < 1
  rw [div_lt_one hden]
  exact_mod_cast hdata.2.2.1

private theorem hybridResidualFractionRat_injectiveOn
    {M Q : Nat} (hM : 0 < M) :
    Set.InjOn (hybridResidualFractionRat M)
      (↑(hybridResidualFractionCarrier M Q) : Set (Nat × Nat)) := by
  intro left hleft right hright hequal
  have hleftData := mem_hybridResidualFractionCarrier_iff.mp hleft
  have hrightData := mem_hybridResidualFractionCarrier_iff.mp hright
  have hleftQ : 0 < left.1 := lt_of_lt_of_le Nat.zero_lt_one hleftData.1
  have hrightQ : 0 < right.1 := lt_of_lt_of_le Nat.zero_lt_one hrightData.1
  have hunique := Rat.div_int_inj
    (by exact_mod_cast Nat.mul_pos hM hleftQ :
      (0 : Int) < (M * left.1 : Int))
    (by exact_mod_cast Nat.mul_pos hM hrightQ :
      (0 : Int) < (M * right.1 : Int))
    (intNatAbs_coprime_of_natCoprime_residual hleftData.2.2.2)
    (intNatAbs_coprime_of_natCoprime_residual hrightData.2.2.2)
    (by simpa [hybridResidualFractionRat] using hequal)
  apply Prod.ext
  · apply Nat.eq_of_mul_eq_mul_left hM
    exact_mod_cast hunique.2
  · exact_mod_cast hunique.1

/-- The residual fractions are separated at the common-factor Farey scale. -/
theorem one_div_mul_sq_le_dist_hybridResidualFractionValue
    {M Q : Nat} (hM : 0 < M) (hQ : 0 < Q) :
    ∀ left ∈ hybridResidualFractionCarrier M Q,
      ∀ right ∈ hybridResidualFractionCarrier M Q, left ≠ right ->
        1 / ((M : Real) * (Q : Real) ^ 2) ≤
          dist ((hybridResidualFractionValue M left : Real) : UnitAddCircle)
            ((hybridResidualFractionValue M right : Real) : UnitAddCircle) := by
  intro left hleft right hright hne
  have hratNe :
      hybridResidualFractionRat M left ≠ hybridResidualFractionRat M right := by
    intro hrat
    exact hne (hybridResidualFractionRat_injectiveOn hM hleft hright hrat)
  have hcircleNe := unitAddCircle_rat_ne_of_mem_Ico
    (hybridResidualFractionRat_nonneg hM hleft)
    (hybridResidualFractionRat_lt_one hM hleft)
    (hybridResidualFractionRat_nonneg hM hright)
    (hybridResidualFractionRat_lt_one hM hright) hratNe
  have hleftDen :
      ((hybridResidualFractionRat M left).den : Real) ≤ (M : Real) * Q := by
    rw [hybridResidualFractionRat_den_eq hM hleft]
    exact_mod_cast Nat.mul_le_mul_left M
      (mem_hybridResidualFractionCarrier_iff.mp hleft).2.1
  have hrightDen :
      ((hybridResidualFractionRat M right).den : Real) ≤ (M : Real) * Q := by
    rw [hybridResidualFractionRat_den_eq hM hright]
    exact_mod_cast Nat.mul_le_mul_left M
      (mem_hybridResidualFractionCarrier_iff.mp hright).2.1
  have hspacing := natCast_div_sq_le_dist_rat_of_den_le
    hM (mul_pos (by exact_mod_cast hM) (by exact_mod_cast hQ))
    (by
      rw [hybridResidualFractionRat_den_eq hM hleft]
      exact dvd_mul_right M left.1)
    (by
      rw [hybridResidualFractionRat_den_eq hM hright]
      exact dvd_mul_right M right.1)
    hleftDen hrightDen hcircleNe
  have hcast (x : Nat × Nat) :
      (hybridResidualFractionRat M x : Real) =
        hybridResidualFractionValue M x := by
    norm_num [hybridResidualFractionRat, hybridResidualFractionValue]
  rw [hcast left, hcast right] at hspacing
  have halgebra :
      (M : Real) / ((M : Real) * Q) ^ 2 =
        1 / ((M : Real) * (Q : Real) ^ 2) := by
    field_simp
  rwa [halgebra] at hspacing

/-- Squared-transform sampling on the residual reduced-fraction carrier. -/
theorem sum_hybridResidualFractionCarrier_le
    (digit : Fin 10) (length M Q : Nat) (hM : 0 < M) (hQ : 0 < Q)
    {delta K : Real} (hdelta : 0 ≤ delta)
    (hscale : 10 ^ length ≤ M * Q ^ 2)
    (hdensity : delta * ((10 ^ length : Nat) : Real) ≤ K) :
    (∑ x ∈ hybridResidualFractionCarrier M Q,
      closedWindowMaximum
        (normalizedPaddedDigitFourierMagnitudeSqAt digit length) delta
        (hybridResidualFractionValue M x)) ≤
      36 * (1 + 2 * K) * ((M : Real) * (Q : Real) ^ 2) /
        (9 : Real) ^ length := by
  have hL : (1 : Real) ≤ (M : Real) * (Q : Real) ^ 2 := by
    have hM1 : (1 : Real) ≤ M := by exact_mod_cast hM
    have hQ1 : (1 : Real) ≤ Q := by exact_mod_cast hQ
    have hQsq : (1 : Real) ≤ (Q : Real) ^ 2 := by nlinarith
    nlinarith [mul_le_mul hM1 hQsq (by norm_num : (0 : Real) ≤ 1)
      (by positivity : (0 : Real) ≤ M)]
  have hK : 0 ≤ K :=
    (mul_nonneg hdelta (by positivity)).trans hdensity
  have hscaleReal :
      ((10 ^ length : Nat) : Real) ≤ (M : Real) * (Q : Real) ^ 2 := by
    exact_mod_cast hscale
  simpa only [add_zero] using
    sum_closedWindowMaximum_normalizedPaddedDigitFourierMagnitudeSqAt_le_of_decimalScale
      (hybridResidualFractionCarrier M Q) digit length
      (hybridResidualFractionValue M) hL hdelta hK hscaleReal hdensity
      (one_div_mul_sq_le_dist_hybridResidualFractionValue hM hQ) 0

end

end PrimesRestrictedDigits
