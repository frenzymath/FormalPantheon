import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSecondEndpoint
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceNormalizedHighSeed

/-!
# Source-normalized scalar recurrence reserve

This isolates the weak scalar gate used after the endpoint and normalized error terms in
Iwaniec's Eq. (8.14). The second-weight coefficient remains a parameter.
-/

namespace PrimesRestrictedDigits

/-- The explicit weak reserve for the normalized Eq. (8.14) bracket. -/
theorem dimensionOneRosserSourceRecurrenceReserve_le
    {E L s0 : Real} (_hE : 0 <= E) (hL : 1 <= L) (hs0 : 1 <= s0)
    (hsmall : 6 * E <= L ^ (1 / 24 : Real)) :
    (1 - 1 / s0) ^ (2 / 3 : Real) +
          E / s0 * L ^ (-1 / 24 : Real) <=
        1 - 1 / (2 * s0) := by
  have hLPos : 0 < L := zero_lt_one.trans_le hL
  have hs0Pos : 0 < s0 := zero_lt_one.trans_le hs0
  have hp : 0 < L ^ (1 / 24 : Real) := Real.rpow_pos_of_pos hLPos _
  have hnormalized : E * L ^ (-1 / 24 : Real) <= 1 / 6 := by
    rw [show (-1 / 24 : Real) = -(1 / 24 : Real) by ring,
      Real.rpow_neg hLPos.le]
    change E / (L ^ (1 / 24 : Real)) <= 1 / 6
    rw [div_le_iff₀ hp]
    nlinarith
  have herror : E / s0 * L ^ (-1 / 24 : Real) <= 1 / (6 * s0) := by
    rw [show E / s0 * L ^ (-1 / 24 : Real) =
      (E * L ^ (-1 / 24 : Real)) / s0 by ring]
    calc
      (E * L ^ (-1 / 24 : Real)) / s0 <= (1 / 6 : Real) / s0 :=
        (div_le_div_iff_of_pos_right hs0Pos).2 hnormalized
      _ = 1 / (6 * s0) := by ring
  calc
    (1 - 1 / s0) ^ (2 / 3 : Real) +
          E / s0 * L ^ (-1 / 24 : Real) <=
        (1 - 2 / (3 * s0)) + 1 / (6 * s0) :=
      add_le_add (dimensionOneRosserSecondEndpointRpow_le_linear hs0) herror
    _ = 1 - 1 / (2 * s0) := by field_simp; ring

/-- An eventual threshold version of the source recurrence reserve. -/
theorem exists_dimensionOneRosserSourceRecurrenceReserve
    {E : Real} (hE : 0 <= E) :
    exists L0 : Real, 1 <= L0 /\
      forall {L s0 : Real}, L0 <= L -> 1 <= s0 ->
        (1 - 1 / s0) ^ (2 / 3 : Real) +
              E / s0 * L ^ (-1 / 24 : Real) <=
            1 - 1 / (2 * s0) := by
  let B : Real := max 1 (6 * E)
  let L0 : Real := B ^ 24
  have hBOne : 1 <= B := le_max_left _ _
  have hBNonneg : 0 <= B := zero_le_one.trans hBOne
  have hBError : 6 * E <= B := le_max_right _ _
  have hL0One : 1 <= L0 := by
    dsimp [L0]
    exact one_le_pow₀ hBOne
  refine ⟨L0, hL0One, ?_⟩
  intro L s0 hL hs0
  have hLOne : 1 <= L := hL0One.trans hL
  have hpow : L0 ^ (1 / 24 : Real) <= L ^ (1 / 24 : Real) :=
    Real.rpow_le_rpow (by positivity) hL (by norm_num)
  have hroot : L0 ^ (1 / 24 : Real) = B := by
    dsimp [L0]
    convert Real.pow_rpow_inv_natCast hBNonneg
      (by norm_num : (24 : Nat) ≠ 0) using 1; norm_num
  apply dimensionOneRosserSourceRecurrenceReserve_le hE hLOne hs0
  rw [hroot] at hpow
  exact hBError.trans hpow

end PrimesRestrictedDigits
