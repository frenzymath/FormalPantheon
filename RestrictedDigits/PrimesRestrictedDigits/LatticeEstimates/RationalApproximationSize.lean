import PrimesRestrictedDigits.LatticeEstimates.RationalApproximationSeparation
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Size of two rational approximations

This is the direct cross-difference kernel repairing published Lemma 14.2. It proves a
stronger all-`X` estimate and does not use continued fractions.
-/

namespace PrimesRestrictedDigits

/-- A common approximation with constant `C` and one reduced source-band
approximation force the source scales to have size `O((X/P)^2)`. -/
theorem rationalApproximationSize_of_commonApproximation
    {X : Nat} (a : Fin X) {P Q E C : Real} {q : Nat} {b : Int}
    (hX : 1 <= X) (hP : 0 < P) (hC : 1 <= C)
    (hQ : 1 <= Q) (hQupper : Q <= Real.sqrt (X : Real))
    (hE : 0 <= E)
    (hEupper : E <= 100 * Real.sqrt (X : Real) / Q)
    (hq : 1 <= q)
    (hqUpper : (q : Real) <= C * (X : Real) / P)
    (hcommon :
      |(((a : Nat) : Real) / (X : Real) -
        (b : Real) / (q : Real))| <= C / (P * (q : Real)))
    (ha : a ∈ latticeRationalApproximationBand Q E) :
    Q + E <= 101 ^ 3 * C ^ 2 * ((X : Real) / P) ^ 2 := by
  obtain ⟨c, r, hr, hrUpper, hrLower, hcoprime, hsource⟩ :=
    mem_latticeRationalApproximationBand_iff.mp ha
  let x : Real := ((a : Nat) : Real) / (X : Real)
  let S : Real := Real.sqrt (X : Real)
  let D : Int := rationalApproximationCrossDifference b c q r
  have hXReal : (1 : Real) <= (X : Real) := by exact_mod_cast hX
  have hXpos : (0 : Real) < (X : Real) := zero_lt_one.trans_le hXReal
  have hPnonneg : 0 <= P := hP.le
  have hCnonneg : 0 <= C := zero_le_one.trans hC
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hqPos : (0 : Real) < q := by exact_mod_cast hq
  have hrPos : (0 : Real) < r := by exact_mod_cast hr
  have hSnonneg : 0 <= S := by
    dsimp only [S]
    exact Real.sqrt_nonneg _
  have hSsq : S ^ 2 = (X : Real) := by
    dsimp only [S]
    exact Real.sq_sqrt (by positivity)
  have hSOne : (1 : Real) <= S := by
    apply (sq_le_sq₀ (by norm_num) hSnonneg).mp
    simpa only [one_pow, hSsq] using hXReal
  have hSleX : S <= (X : Real) := by
    calc
      S = S * 1 := by ring
      _ <= S * S := mul_le_mul_of_nonneg_left hSOne hSnonneg
      _ = (X : Real) := by rw [← sq, hSsq]
  have hQE : Q * E <= 100 * S := by
    apply (le_div_iff₀ hQpos).mp at hEupper
    dsimp only [S]
    nlinarith
  have hErough : E <= 100 * S := by
    calc
      E <= Q * E := by nlinarith
      _ <= 100 * S := hQE
  have hsourceScale : Q + E <= 101 * S := by
    linarith
  have hQoneE : Q * (1 + E) <= 101 * S := by
    calc
      Q * (1 + E) = Q + Q * E := by ring
      _ <= S + 100 * S := add_le_add hQupper hQE
      _ = 101 * S := by ring
  have hsourceUpper :
      |x - (c : Real) / (r : Real)| <= E / (X : Real) := by
    simpa only [x] using latticeRationalErrorInBand_abs_le hsource
  have hdetInitial :
      |(D : Real)| <=
        (q : Real) * (r : Real) *
          (C / (P * (q : Real)) + E / (X : Real)) := by
    have hcross := abs_rationalApproximationCrossDifference_le
      x b c q r (lt_of_lt_of_le Nat.zero_lt_one hq)
        (lt_of_lt_of_le Nat.zero_lt_one hr)
    calc
      |(D : Real)| <=
          (q : Real) * (r : Real) *
            (|x - (b : Real) / (q : Real)| +
              |x - (c : Real) / (r : Real)|) := by
        simpa only [D] using hcross
      _ <= (q : Real) * (r : Real) *
          (C / (P * (q : Real)) + E / (X : Real)) := by
        gcongr
  have hdetBound : |(D : Real)| <= C * Q * (1 + E) / P := by
    calc
      |(D : Real)| <=
          (q : Real) * (r : Real) *
            (C / (P * (q : Real)) + E / (X : Real)) := hdetInitial
      _ = (r : Real) * C / P +
          (q : Real) * (r : Real) * E / (X : Real) := by
        field_simp [hP.ne', hqPos.ne', hXpos.ne']

      _ <= Q * C / P +
          (C * (X : Real) / P) * Q * E / (X : Real) := by
        gcongr
      _ = C * Q * (1 + E) / P := by
        field_simp [hP.ne', hXpos.ne']

  by_cases hsmall : P <= 101 * C * S
  · have hrightNonneg : 0 <= 101 * C * S := by positivity
    have hPsq : P ^ 2 <= (101 * C * S) ^ 2 :=
      (sq_le_sq₀ hPnonneg hrightNonneg).2 hsmall
    have hScube : S ^ 3 <= S ^ 4 := by
      calc
        S ^ 3 = S ^ 3 * 1 := by ring
        _ <= S ^ 3 * S := mul_le_mul_of_nonneg_left hSOne (by positivity)
        _ = S ^ 4 := by ring
    have hproduct :
        (Q + E) * P ^ 2 <=
          101 ^ 3 * C ^ 2 * (X : Real) ^ 2 := by
      calc
        (Q + E) * P ^ 2 <= (101 * S) * P ^ 2 :=
          mul_le_mul_of_nonneg_right hsourceScale (sq_nonneg P)
        _ <= (101 * S) * (101 * C * S) ^ 2 :=
          mul_le_mul_of_nonneg_left hPsq (by positivity)
        _ = 101 ^ 3 * C ^ 2 * S ^ 3 := by ring
        _ <= 101 ^ 3 * C ^ 2 * S ^ 4 := by gcongr
        _ = 101 ^ 3 * C ^ 2 * (X : Real) ^ 2 := by
          rw [← hSsq]
          ring
    calc
      Q + E <=
          (101 ^ 3 * C ^ 2 * (X : Real) ^ 2) / P ^ 2 :=
        (le_div_iff₀ (sq_pos_of_pos hP)).2 hproduct
      _ = 101 ^ 3 * C ^ 2 * ((X : Real) / P) ^ 2 := by
        rw [div_pow]
        ring
  · have hlarge : 101 * C * S < P := lt_of_not_ge hsmall
    have hdetLt : |(D : Real)| < 1 := by
      calc
        |(D : Real)| <= C * Q * (1 + E) / P := hdetBound
        _ <= C * (101 * S) / P := by
          apply div_le_div_of_nonneg_right _ hPnonneg
          simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_left hQoneE hCnonneg
        _ < 1 := by
          apply (div_lt_one hP).2
          nlinarith
    have hDzero : D = 0 := by
      by_contra hD
      have hone := one_le_abs_crossDifference_cast
        (b := b) (c := c) (q := q) (r := r) (by simpa only [D] using hD)
      linarith
    have hrDvd : r ∣ q :=
      sourceDenominator_dvd_of_crossDifference_eq_zero hcoprime
        (by simpa only [D] using hDzero)
    have hrLeq : r <= q := Nat.le_of_dvd
      (lt_of_lt_of_le Nat.zero_lt_one hq) hrDvd
    have hrLeqReal : (r : Real) <= q := by exact_mod_cast hrLeq
    have hQlinear : Q <= 10 * C * (X : Real) / P := by
      calc
        Q <= 10 * (r : Real) := hrLower.le
        _ <= 10 * (q : Real) := by gcongr
        _ <= 10 * (C * (X : Real) / P) := by gcongr
        _ = 10 * C * (X : Real) / P := by ring
    have hfraction :
        (b : Real) / (q : Real) = (c : Real) / (r : Real) :=
      div_eq_div_of_crossDifference_eq_zero
        (lt_of_lt_of_le Nat.zero_lt_one hq)
        (lt_of_lt_of_le Nat.zero_lt_one hr)
        (by simpa only [D] using hDzero)
    have hsourceCommon :
        |x - (c : Real) / (r : Real)| <= C / (P * (q : Real)) := by
      rw [← hfraction]
      simpa only [x] using hcommon
    have hElinear : E <= 10 * C * (X : Real) / P := by
      rcases hsource with ⟨hEzero, _⟩ | ⟨hEpos, hlower, _⟩
      · rw [hEzero]
        positivity
      · have hstrict :
            E / ((X : Real) * 10) < C / (P * (q : Real)) := by
          calc
            E / ((X : Real) * 10) = E / (X : Real) / 10 := by ring
            _ < |x - (c : Real) / (r : Real)| := hlower
            _ <= C / (P * (q : Real)) := hsourceCommon
        have hraw :
            E < (C / (P * (q : Real))) * ((X : Real) * 10) :=
          (div_lt_iff₀ (mul_pos hXpos (by norm_num))).mp hstrict
        have hinvq : (1 : Real) / (q : Real) <= 1 := by
          have hqOneReal : (1 : Real) <= q := by exact_mod_cast hq
          apply (div_le_iff₀ hqPos).2
          simpa only [one_mul] using hqOneReal
        calc
          E <= (C / (P * (q : Real))) * ((X : Real) * 10) := hraw.le
          _ = (10 * C * (X : Real) / P) * (1 / (q : Real)) := by
            field_simp [hP.ne', hqPos.ne']

          _ <= (10 * C * (X : Real) / P) * 1 :=
            mul_le_mul_of_nonneg_left hinvq (by positivity)
          _ = 10 * C * (X : Real) / P := by ring
    have hlinear : Q + E <= 20 * C * ((X : Real) / P) := by
      calc
        Q + E <= 10 * C * (X : Real) / P +
            10 * C * (X : Real) / P := add_le_add hQlinear hElinear
        _ = 20 * C * ((X : Real) / P) := by ring
    have hYpos : 0 < (X : Real) / P := div_pos hXpos hP
    have hCY : 1 <= C * ((X : Real) / P) := by
      calc
        (1 : Real) <= q := by exact_mod_cast hq
        _ <= C * (X : Real) / P := hqUpper
        _ = C * ((X : Real) / P) := by ring
    have hYquad :
        (X : Real) / P <= C * ((X : Real) / P) ^ 2 := by
      calc
        (X : Real) / P = ((X : Real) / P) * 1 := by ring
        _ <= ((X : Real) / P) * (C * ((X : Real) / P)) :=
          mul_le_mul_of_nonneg_left hCY hYpos.le
        _ = C * ((X : Real) / P) ^ 2 := by ring
    calc
      Q + E <= 20 * C * ((X : Real) / P) := hlinear
      _ <= 20 * C * (C * ((X : Real) / P) ^ 2) := by gcongr
      _ = 20 * C ^ 2 * ((X : Real) / P) ^ 2 := by ring
      _ <= 101 ^ 3 * C ^ 2 * ((X : Real) / P) ^ 2 := by
        gcongr
        norm_num

end PrimesRestrictedDigits
