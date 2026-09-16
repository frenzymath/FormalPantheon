import PrimesRestrictedDigits.Fourier.LargeSieveScaleSelection

/-!
# Decimal block selection for hybrid estimates

This module makes the two successive power-of-ten choices in the low-density branch explicit.
-/

namespace PrimesRestrictedDigits

/-- In the regime `10*L*E < Y`, select decimal prefix, middle, and tail
lengths whose tail scale lies in `[E,100E)`. -/
theorem exists_hybrid_decimalBlocks
    {L E : Real} (hL : 1 <= L) (hE : 1 <= E) (length : Nat)
    (hlow : 10 * L * E < ((10 ^ length : Nat) : Real)) :
    ∃ u v w : Nat,
      length = u + v + w ∧
      (((10 ^ u : Nat) : Real) <= L) ∧
      (L < 10 * ((10 ^ u : Nat) : Real)) ∧
      (((10 ^ v : Nat) : Real) <=
        ((10 ^ length : Nat) : Real) / (L * E)) ∧
      (((10 ^ length : Nat) : Real) / (L * E) <
        10 * ((10 ^ v : Nat) : Real)) ∧
      (E <= ((10 ^ w : Nat) : Real)) ∧
      (((10 ^ w : Nat) : Real) < 100 * E) := by
  let Y : Real := ((10 ^ length : Nat) : Real)
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hE0 : 0 < E := zero_lt_one.trans_le hE
  have hY0 : 0 < Y := by
    dsimp [Y]
    positivity
  have hLE : 1 <= L * E := by nlinarith [mul_le_mul hL hE zero_le_one hL0.le]
  have hratio : 1 <= Y / (L * E) := by
    apply (le_div_iff₀ (mul_pos hL0 hE0)).mpr
    dsimp [Y] at hlow ⊢
    nlinarith
  obtain ⟨v, hvLength, hvRatio, hvY, hvClose, hvExact⟩ :=
    exists_largeSieve_decimalPrefix hratio length
  let V : Real := ((10 ^ v : Nat) : Real)
  have hV0 : 0 < V := by
    dsimp [V]
    positivity
  have hratioY : Y / (L * E) <= Y := by
    apply div_le_self hY0.le hLE
  have hvClose' : Y / (L * E) < 10 * V := by
    change min (Y / (L * E)) Y < 10 * V at hvClose
    rw [min_eq_left hratioY] at hvClose
    exact hvClose
  let remaining := length - v
  let R : Real := ((10 ^ remaining : Nat) : Real)
  have hfactorNat : 10 ^ length = 10 ^ v * 10 ^ remaining := by
    dsimp [remaining]
    rw [← pow_add]
    congr 1
    omega
  have hfactor : Y = V * R := by
    dsimp [Y, V, R]
    exact_mod_cast hfactorNat
  have hVLE : V * (L * E) <= Y := by
    apply (le_div_iff₀ (mul_pos hL0 hE0)).mp
    simpa only [V, Y] using hvRatio
  have hLR : L <= R := by
    have hVL : V * L <= V * (L * E) := by
      nlinarith [mul_nonneg (mul_nonneg hV0.le hL0.le) (sub_nonneg.mpr hE)]
    have hVLR : V * L <= V * R := by
      rw [← hfactor]
      exact hVL.trans hVLE
    exact le_of_mul_le_mul_left hVLR hV0
  obtain ⟨u, huRemaining, huL, huR, huClose, huExact⟩ :=
    exists_largeSieve_decimalPrefix hL remaining
  let U : Real := ((10 ^ u : Nat) : Real)
  have hU0 : 0 < U := by
    dsimp [U]
    positivity
  have huClose' : L < 10 * U := by
    change min L R < 10 * U at huClose
    rw [min_eq_left hLR] at huClose
    exact huClose
  let w := remaining - u
  let W : Real := ((10 ^ w : Nat) : Real)
  have hlength : length = u + v + w := by
    dsimp [w, remaining]
    omega
  have hremainingFactorNat : 10 ^ remaining = 10 ^ u * 10 ^ w := by
    dsimp [w]
    rw [← pow_add]
    congr 1
    omega
  have hremainingFactor : R = U * W := by
    dsimp [R, U, W]
    exact_mod_cast hremainingFactorNat
  have hYFactor : Y = V * U * W := by
    rw [hfactor, hremainingFactor]
    ring
  have hUE : U * E <= L * E :=
    mul_le_mul_of_nonneg_right (by simpa only [U] using huL) hE0.le
  have hVUE : V * (U * E) <= Y := by
    calc
      V * (U * E) <= V * (L * E) :=
        mul_le_mul_of_nonneg_left hUE hV0.le
      _ <= Y := hVLE
  have hEW : E <= W := by
    have hVUE' : V * U * E <= V * U * W := by
      calc
        V * U * E = V * (U * E) := by ring
        _ <= Y := hVUE
        _ = V * U * W := hYFactor
    exact le_of_mul_le_mul_left hVUE' (mul_pos hV0 hU0)
  have hYUpper : Y < 10 * V * L * E := by
    have hscaled := mul_lt_mul_of_pos_right hvClose' (mul_pos hL0 hE0)
    calc
      Y = (Y / (L * E)) * (L * E) := by field_simp
      _ < (10 * V) * (L * E) := hscaled
      _ = 10 * V * L * E := by ring
  have hWUpper : W < 100 * E := by
    have hUL : L < 10 * U := huClose'
    have hYUpper' : V * U * W < 10 * V * L * E := by
      rw [← hYFactor]
      exact hYUpper
    have hfirst : U * W < 10 * L * E := by
      apply lt_of_mul_lt_mul_left _ hV0.le
      nlinarith [hYUpper']
    have hsecond : U * W < U * (100 * E) := by
      calc
        U * W < 10 * L * E := hfirst
        _ < U * (100 * E) := by nlinarith [mul_pos hU0 hE0]
    exact lt_of_mul_lt_mul_left hsecond hU0.le
  refine ⟨u, v, w, hlength, ?_, huClose', ?_, hvClose', hEW, hWUpper⟩
  · simpa only [U] using huL
  · simpa only [V, Y] using hvRatio

end PrimesRestrictedDigits
