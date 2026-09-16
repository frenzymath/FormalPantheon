import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserArtificialFactor
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserHighSeedCalculus

/-!
# Scalar caps for the complete rapid Rosser split

The weak artificial-factor cap uses only the complementary inequality
`s^51 <= L`; it is intentionally independent of the stronger bounded-region
threshold used elsewhere.  The high-seed envelope cap is an immediate
consequence of the inclusive derivative reserve.
-/

namespace PrimesRestrictedDigits

/-- The epsilon-zero artificial factor is bounded by `exp 1` whenever the
coordinate's fifty-first power is below the logarithmic level. -/
theorem dimensionOneRosserArtificialFactor_zero_le_exp_one
    {L s : Real} (hs : 1 <= s) (hpow : s ^ (51 : Nat) <= L) :
    dimensionOneRosserArtificialFactor L 0 s <= Real.exp 1 := by
  have hs0 : 0 <= s := by linarith
  have hspowOne : 1 <= s ^ (51 : Nat) := one_le_pow₀ hs
  have hLOne : 1 <= L := hspowOne.trans hpow
  have hLPos : 0 < L := zero_lt_one.trans_le hLOne
  have hratio : 0 <= s ^ (50 : Nat) / L := by
    exact div_nonneg (pow_nonneg hs0 _) hLPos.le
  have hbasePos : 0 < 1 + s ^ (50 : Nat) / L := by linarith
  have hlog : Real.log (1 + s ^ (50 : Nat) / L) <=
      s ^ (50 : Nat) / L := by
    have h := Real.log_le_sub_one_of_pos hbasePos
    linarith
  have hscaled : s * Real.log (1 + s ^ (50 : Nat) / L) <=
      s * (s ^ (50 : Nat) / L) :=
    mul_le_mul_of_nonneg_left hlog hs0
  have hpowDiv : s ^ (51 : Nat) / L <= (1 : Real) :=
    (div_le_one hLPos).2 hpow
  have hproduct : s * (s ^ (50 : Nat) / L) <= (1 : Real) := by
    calc
      s * (s ^ (50 : Nat) / L) = s ^ (51 : Nat) / L := by ring
      _ <= 1 := hpowDiv
  unfold dimensionOneRosserArtificialFactor
    dimensionOneRosserArtificialBase
  simp only [add_zero]
  apply Real.exp_le_exp.mpr
  exact hscaled.trans hproduct

/-- The independent high-rank seed envelope is below the unit exponential
tail on the inclusive large-coordinate domain. -/
theorem dimensionOneRosserSeedEnvelope_lt_exp_neg
    {s : Real} (hsLarge : Real.exp 5000 <= s) :
    dimensionOneRosserSeedEnvelope s < Real.exp (-s) := by
  have hsPos : 0 < s := (Real.exp_pos 5000).trans_le hsLarge
  have hlogLower : 5000 <= Real.log s :=
    (Real.le_log_iff_exp_le hsPos).2 hsLarge
  have hlogPos : 0 < Real.log s := by
    linarith
  have hinvPos : 0 < 1 / Real.log s := one_div_pos.mpr hlogPos
  have hcoef := dimensionOneRosserSeedEnvelope_derivCoefficient_le hsLarge
  have hfour : 4 - Real.log (dimensionOneRosserSeedTilt s) < -1 := by
    linarith
  have hexponent :
      s * (4 - Real.log (dimensionOneRosserSeedTilt s)) < -s := by
    have hmul := mul_lt_mul_of_pos_left hfour hsPos
    nlinarith
  unfold dimensionOneRosserSeedEnvelope
  exact Real.exp_lt_exp.mpr hexponent

end PrimesRestrictedDigits
