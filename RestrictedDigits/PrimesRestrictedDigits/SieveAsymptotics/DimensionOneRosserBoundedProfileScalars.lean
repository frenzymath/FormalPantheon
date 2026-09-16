import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserBoundedSeedMajorant

/-!
# Common bounded Rosser profile scalars

This factors the two bounded sign profiles through one scalar and proves the fixed-splice
endpoint and terminal budgets used by the later rank recurrence. The stronger level condition
is project-local and does not claim Iwaniec's Eq. (8.14).
-/

open Set

namespace PrimesRestrictedDigits

/-- The quarter of the absolute bounded-seed coefficient assigned to the
unscaled delay component. -/
noncomputable def dimensionOneRosserBoundedSeedShare : Real :=
  dimensionOneRosserBoundedSeedConstant / 4

/-- The common scalar multiplying either bounded delay profile. -/
noncomputable def dimensionOneRosserBoundedProfileScalar
    (L s : Real) : Real :=
  L ^ (-1 / 3 : Real) * dimensionOneRosserArtificialFactor L 0 s +
    dimensionOneRosserBoundedSeedShare

/-- The absolute splice lies strictly above three. -/
theorem three_lt_dimensionOneRosserSecondSplice :
    3 < dimensionOneRosserSecondSplice := by
  unfold dimensionOneRosserSecondSplice
  linarith [Real.exp_pos (5000 : Real)]

/-- The bounded seed share is strictly positive. -/
theorem dimensionOneRosserBoundedSeedShare_pos :
    0 < dimensionOneRosserBoundedSeedShare := by
  unfold dimensionOneRosserBoundedSeedShare
  nlinarith [one_le_dimensionOneRosserBoundedSeedConstant]

/-- The common delay floor is at most one. -/
theorem dimensionOneRosserBoundedDelayFloor_le_one :
    dimensionOneRosserBoundedDelayFloor <= 1 := by
  have hPlusAtSplice :
      dimensionOneDelayScaledPlus dimensionOneRosserSecondSplice <=
        dimensionOneDelayScaledPlus 1 :=
    dimensionOneDelayScaledPlus_antitoneOn
      (show (1 : Real) ∈ Ici 1 by norm_num)
      (show dimensionOneRosserSecondSplice ∈ Ici (1 : Real) by
        exact one_le_dimensionOneRosserSecondSplice)
      one_le_dimensionOneRosserSecondSplice
  calc
    dimensionOneRosserBoundedDelayFloor <=
        dimensionOneDelayScaledPlus dimensionOneRosserSecondSplice :=
      min_le_left _ _
    _ <= dimensionOneDelayScaledPlus 1 := hPlusAtSplice
    _ = 1 / 2 := dimensionOneDelayScaledPlus_eq_half_of_le (by norm_num)
    _ <= 1 := by norm_num

/-- The common profile scalar is positive at every positive logarithmic
level. -/
theorem dimensionOneRosserBoundedProfileScalar_pos
    {L s : Real} (hL : 0 < L) :
    0 < dimensionOneRosserBoundedProfileScalar L s := by
  unfold dimensionOneRosserBoundedProfileScalar
  exact add_pos
    (mul_pos (Real.rpow_pos_of_pos hL _)
      (Real.exp_pos _))
    dimensionOneRosserBoundedSeedShare_pos

/-- The bounded plus majorant has the common scalar factor. -/
theorem dimensionOneRosserBoundedPlusMajorant_eq_scalar_mul
    (L s : Real) :
    dimensionOneRosserBoundedPlusMajorant L s =
      dimensionOneRosserBoundedProfileScalar L s *
        dimensionOneDelayScaledPlus s := by
  unfold dimensionOneRosserBoundedPlusMajorant
    dimensionOneRosserBoundedProfileScalar
    dimensionOneRosserBoundedSeedShare
  ring

/-- The bounded minus majorant has the common scalar factor. -/
theorem dimensionOneRosserBoundedMinusMajorant_eq_scalar_mul
    (L s : Real) :
    dimensionOneRosserBoundedMinusMajorant L s =
      dimensionOneRosserBoundedProfileScalar L s *
        dimensionOneDelayScaledMinus s := by
  unfold dimensionOneRosserBoundedMinusMajorant
    dimensionOneRosserBoundedProfileScalar
    dimensionOneRosserBoundedSeedShare
  ring

private theorem fixedSpliceEndpointCoefficient_le
    {K L s : Real} (hK : 0 <= K) (hL : 0 < L) (hs : 2 <= s)
    (hfixed :
      48 * K * dimensionOneRosserSecondSplice ^ 2 <=
        L * dimensionOneRosserBoundedDelayFloor) :
    2 * K * dimensionOneRosserSecondSplice /
          (L * (1 - 1 / s)) <=
      dimensionOneRosserBoundedDelayFloor /
        (12 * dimensionOneRosserSecondSplice) := by
  have hU : 0 < dimensionOneRosserSecondSplice :=
    zero_lt_one.trans_le one_le_dimensionOneRosserSecondSplice
  have hsPos : 0 < s := by linarith
  have hbase : 0 < 1 - 1 / s := by
    have hinv : 1 / s <= (1 / 2 : Real) :=
      one_div_le_one_div_of_le (by norm_num) hs
    linarith
  have hbaseInv : (1 - 1 / s)⁻¹ <= (2 : Real) := by
    rw [inv_le_iff_one_le_mul₀ hbase]
    have hinv : 1 / s <= (1 / 2 : Real) :=
      one_div_le_one_div_of_le (by norm_num) hs
    nlinarith
  have hprefix : 0 <=
      2 * K * dimensionOneRosserSecondSplice / L := by positivity
  have hcoarse :
      2 * K * dimensionOneRosserSecondSplice /
            (L * (1 - 1 / s)) <=
        4 * K * dimensionOneRosserSecondSplice / L := by
    calc
      2 * K * dimensionOneRosserSecondSplice /
            (L * (1 - 1 / s)) =
          (2 * K * dimensionOneRosserSecondSplice / L) *
            (1 - 1 / s)⁻¹ := by
        field_simp [hL.ne', hbase.ne']
      _ <= (2 * K * dimensionOneRosserSecondSplice / L) * 2 :=
        mul_le_mul_of_nonneg_left hbaseInv hprefix
      _ = 4 * K * dimensionOneRosserSecondSplice / L := by ring
  apply hcoarse.trans
  rw [div_le_div_iff₀ hL (mul_pos (by norm_num) hU)]
  nlinarith

private theorem fixedSpliceEndpointCoefficient_nonneg
    {K L s : Real} (hK : 0 <= K) (hL : 0 < L) (hs : 2 <= s) :
    0 <= 2 * K * dimensionOneRosserSecondSplice /
      (L * (1 - 1 / s)) := by
  have hinv : 1 / s <= (1 / 2 : Real) :=
    one_div_le_one_div_of_le (by norm_num) hs
  have hbase : 0 < 1 - 1 / s := by linarith
  have hU : 0 <= dimensionOneRosserSecondSplice :=
    zero_le_one.trans one_le_dimensionOneRosserSecondSplice
  exact div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hK) hU)
    (mul_nonneg hL.le hbase.le)

/-- At the fixed splice, the shifted-minus endpoint consumes at most
`1/(12*U)` of the current plus delay. -/
theorem dimensionOneRosserPlusFixedSpliceEndpoint_le
    {K L s : Real} (hK : 0 <= K) (hL : 0 < L)
    (hs : 3 <= s) (hsU : s <= dimensionOneRosserSecondSplice)
    (hfixed :
      48 * K * dimensionOneRosserSecondSplice ^ 2 <=
        L * dimensionOneRosserBoundedDelayFloor) :
    (2 * K * dimensionOneRosserSecondSplice /
        (L * (1 - 1 / s))) *
          dimensionOneDelayScaledMinus (s - 1) <=
      dimensionOneDelayScaledPlus s /
        (12 * dimensionOneRosserSecondSplice) := by
  have hshift : dimensionOneDelayScaledMinus (s - 1) <= 1 := by
    calc
      dimensionOneDelayScaledMinus (s - 1) <=
          dimensionOneDelayScaledMinus 2 :=
        dimensionOneDelayScaledMinus_antitoneOn
          (show (2 : Real) ∈ Ici 2 by norm_num)
          (show s - 1 ∈ Ici (2 : Real) by change 2 <= s - 1; linarith)
          (by linarith)
      _ = 1 := dimensionOneDelayScaledMinus_eq_one_of_le le_rfl
  have hfloor : dimensionOneRosserBoundedDelayFloor <=
      dimensionOneDelayScaledPlus s := by
    calc
      dimensionOneRosserBoundedDelayFloor <=
          dimensionOneDelayScaledPlus dimensionOneRosserSecondSplice :=
        min_le_left _ _
      _ <= dimensionOneDelayScaledPlus s :=
        dimensionOneDelayScaledPlus_antitoneOn
          (show s ∈ Ici (1 : Real) by change 1 <= s; linarith)
          (show dimensionOneRosserSecondSplice ∈ Ici (1 : Real) by
            exact one_le_dimensionOneRosserSecondSplice)
          hsU
  have hcoeff0 := fixedSpliceEndpointCoefficient_nonneg hK hL
    (by linarith : 2 <= s)
  calc
    (2 * K * dimensionOneRosserSecondSplice /
          (L * (1 - 1 / s))) *
        dimensionOneDelayScaledMinus (s - 1) <=
      (2 * K * dimensionOneRosserSecondSplice /
          (L * (1 - 1 / s))) * 1 :=
        mul_le_mul_of_nonneg_left hshift hcoeff0
    _ <= dimensionOneRosserBoundedDelayFloor /
        (12 * dimensionOneRosserSecondSplice) := by
      simpa using fixedSpliceEndpointCoefficient_le hK hL
        (by linarith : 2 <= s) hfixed
    _ <= dimensionOneDelayScaledPlus s /
        (12 * dimensionOneRosserSecondSplice) :=
      div_le_div_of_nonneg_right hfloor
        (mul_nonneg (by norm_num)
          (zero_le_one.trans one_le_dimensionOneRosserSecondSplice))

/-- At the fixed splice, the shifted-plus endpoint consumes at most
`1/(12*U)` of the current minus delay. -/
theorem dimensionOneRosserMinusFixedSpliceEndpoint_le
    {K L s : Real} (hK : 0 <= K) (hL : 0 < L)
    (hs : 2 <= s) (hsU : s <= dimensionOneRosserSecondSplice)
    (hfixed :
      48 * K * dimensionOneRosserSecondSplice ^ 2 <=
        L * dimensionOneRosserBoundedDelayFloor) :
    (2 * K * dimensionOneRosserSecondSplice /
        (L * (1 - 1 / s))) *
          dimensionOneDelayScaledPlus (s - 1) <=
      dimensionOneDelayScaledMinus s /
        (12 * dimensionOneRosserSecondSplice) := by
  have hshift : dimensionOneDelayScaledPlus (s - 1) <= 1 := by
    calc
      dimensionOneDelayScaledPlus (s - 1) <=
          dimensionOneDelayScaledPlus 1 :=
        dimensionOneDelayScaledPlus_antitoneOn
          (show (1 : Real) ∈ Ici 1 by norm_num)
          (show s - 1 ∈ Ici (1 : Real) by change 1 <= s - 1; linarith)
          (by linarith)
      _ = 1 / 2 := dimensionOneDelayScaledPlus_eq_half_of_le
        (by norm_num : (1 : Real) <= 3)
      _ <= 1 := by norm_num
  have hfloor : dimensionOneRosserBoundedDelayFloor <=
      dimensionOneDelayScaledMinus s := by
    calc
      dimensionOneRosserBoundedDelayFloor <=
          dimensionOneDelayScaledMinus dimensionOneRosserSecondSplice :=
        min_le_right _ _
      _ <= dimensionOneDelayScaledMinus s :=
        dimensionOneDelayScaledMinus_antitoneOn
          (show s ∈ Ici (2 : Real) by exact hs)
          (show dimensionOneRosserSecondSplice ∈ Ici (2 : Real) by
            change 2 <= dimensionOneRosserSecondSplice
            linarith [three_lt_dimensionOneRosserSecondSplice])
          hsU
  have hcoeff0 := fixedSpliceEndpointCoefficient_nonneg hK hL hs
  calc
    (2 * K * dimensionOneRosserSecondSplice /
          (L * (1 - 1 / s))) *
        dimensionOneDelayScaledPlus (s - 1) <=
      (2 * K * dimensionOneRosserSecondSplice /
          (L * (1 - 1 / s))) * 1 :=
        mul_le_mul_of_nonneg_left hshift hcoeff0
    _ <= dimensionOneRosserBoundedDelayFloor /
        (12 * dimensionOneRosserSecondSplice) := by
      simpa using fixedSpliceEndpointCoefficient_le hK hL hs hfixed
    _ <= dimensionOneDelayScaledMinus s /
        (12 * dimensionOneRosserSecondSplice) :=
      div_le_div_of_nonneg_right hfloor
        (mul_nonneg (by norm_num)
          (zero_le_one.trans one_le_dimensionOneRosserSecondSplice))

/-- The density conversion and the half-seed budget fit inside the fixed
terminal contraction. -/
theorem dimensionOneRosserFixedSpliceDensityHalf_le
    {K L : Real} (hK : 0 <= K) (hL : 0 < L)
    (hfixed :
      48 * K * dimensionOneRosserSecondSplice ^ 2 <=
        L * dimensionOneRosserBoundedDelayFloor) :
    (1 + K * dimensionOneRosserSecondSplice / L) / 2 <=
      1 - 1 / dimensionOneRosserSecondSplice := by
  have hU := three_lt_dimensionOneRosserSecondSplice
  have hU0 : 0 < dimensionOneRosserSecondSplice := by linarith
  have hLfloor :
      L * dimensionOneRosserBoundedDelayFloor <= L := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      dimensionOneRosserBoundedDelayFloor_le_one hL.le
  have hlarge :
      48 * K * dimensionOneRosserSecondSplice <= L := by
    calc
      48 * K * dimensionOneRosserSecondSplice <=
          48 * K * dimensionOneRosserSecondSplice ^ 2 := by
        have hmul : 0 <= 48 * K := mul_nonneg (by norm_num) hK
        exact mul_le_mul_of_nonneg_left
          (by nlinarith [one_le_dimensionOneRosserSecondSplice]) hmul
      _ <= L * dimensionOneRosserBoundedDelayFloor := hfixed
      _ <= L := hLfloor
  have hratio : K * dimensionOneRosserSecondSplice / L <= 1 / 48 := by
    rw [div_le_iff₀ hL]
    nlinarith
  have hinvU : 1 / dimensionOneRosserSecondSplice < 1 / 3 := by
    exact one_div_lt_one_div_of_lt (by norm_num) hU
  nlinarith

private theorem fixedSpliceBracket_le
    {current terminal endpoint : Real}
    (hendpoint : endpoint <=
      current / (12 * dimensionOneRosserSecondSplice)) :
    (1 - 1 / dimensionOneRosserSecondSplice) *
          (current - terminal) + endpoint <=
      (1 - 11 / (12 * dimensionOneRosserSecondSplice)) * current -
        (1 - 1 / dimensionOneRosserSecondSplice) * terminal := by
  calc
    (1 - 1 / dimensionOneRosserSecondSplice) *
          (current - terminal) + endpoint <=
        (1 - 1 / dimensionOneRosserSecondSplice) *
          (current - terminal) +
            current / (12 * dimensionOneRosserSecondSplice) :=
      add_le_add_right hendpoint _
    _ = (1 - 11 / (12 * dimensionOneRosserSecondSplice)) * current -
        (1 - 1 / dimensionOneRosserSecondSplice) * terminal := by ring

private theorem fixedSpliceSeedTransport_le_terminal
    {K L terminal : Real} (hK : 0 <= K) (hL : 0 < L)
    (hfixed :
      48 * K * dimensionOneRosserSecondSplice ^ 2 <=
        L * dimensionOneRosserBoundedDelayFloor)
    (hseed : dimensionOneRosserSeedEnvelope dimensionOneRosserSecondSplice <=
      dimensionOneRosserBoundedSeedShare * terminal)
    (hterminal : 0 <= terminal) :
    (1 + K * dimensionOneRosserSecondSplice / L) *
        (dimensionOneRosserSeedEnvelope dimensionOneRosserSecondSplice / 2) <=
      dimensionOneRosserBoundedSeedShare *
        (1 - 1 / dimensionOneRosserSecondSplice) * terminal := by
  have hratio0 : 0 <= 1 + K * dimensionOneRosserSecondSplice / L := by
    have hU0 : 0 < dimensionOneRosserSecondSplice := by
      linarith [three_lt_dimensionOneRosserSecondSplice]
    positivity
  have hhalf := dimensionOneRosserFixedSpliceDensityHalf_le hK hL hfixed
  calc
    (1 + K * dimensionOneRosserSecondSplice / L) *
          (dimensionOneRosserSeedEnvelope dimensionOneRosserSecondSplice / 2) <=
        (1 + K * dimensionOneRosserSecondSplice / L) *
          (dimensionOneRosserBoundedSeedShare * terminal / 2) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hseed (by norm_num)) hratio0
    _ = ((1 + K * dimensionOneRosserSecondSplice / L) / 2) *
        (dimensionOneRosserBoundedSeedShare * terminal) := by ring
    _ <= (1 - 1 / dimensionOneRosserSecondSplice) *
        (dimensionOneRosserBoundedSeedShare * terminal) :=
      mul_le_mul_of_nonneg_right hhalf
        (mul_nonneg dimensionOneRosserBoundedSeedShare_pos.le hterminal)
    _ = dimensionOneRosserBoundedSeedShare *
        (1 - 1 / dimensionOneRosserSecondSplice) * terminal := by ring

/-- The transported high seed and the bounded plus shell fit the retained
plus contraction. -/
theorem dimensionOneRosserPlusFixedSpliceBudget_le
    {K L s : Real} (hK : 0 <= K) (hL : 0 < L)
    (hs : 3 <= s) (hsU : s <= dimensionOneRosserSecondSplice)
    (hfixed :
      48 * K * dimensionOneRosserSecondSplice ^ 2 <=
        L * dimensionOneRosserBoundedDelayFloor) :
    (1 + K * dimensionOneRosserSecondSplice / L) *
          (dimensionOneRosserSeedEnvelope dimensionOneRosserSecondSplice / 2) +
        dimensionOneRosserBoundedSeedShare *
          ((1 - 1 / dimensionOneRosserSecondSplice) *
              (dimensionOneDelayScaledPlus s -
                dimensionOneDelayScaledPlus dimensionOneRosserSecondSplice) +
            (2 * K * dimensionOneRosserSecondSplice /
                (L * (1 - 1 / s))) *
              dimensionOneDelayScaledMinus (s - 1)) <=
      dimensionOneRosserBoundedSeedShare *
        ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) *
          dimensionOneDelayScaledPlus s) := by
  have hterminal := dimensionOneDelayScaledPlus_pos
    (show 0 < dimensionOneRosserSecondSplice by
      linarith [three_lt_dimensionOneRosserSecondSplice])
  have hseed := dimensionOneRosserSeedEnvelope_le_boundedPlus
    one_le_dimensionOneRosserSecondSplice le_rfl
  change dimensionOneRosserSeedEnvelope dimensionOneRosserSecondSplice <=
    dimensionOneRosserBoundedSeedShare *
      dimensionOneDelayScaledPlus dimensionOneRosserSecondSplice at hseed
  have hhigh := fixedSpliceSeedTransport_le_terminal hK hL hfixed hseed
    hterminal.le
  have hbracket := fixedSpliceBracket_le
    (current := dimensionOneDelayScaledPlus s)
    (terminal :=
      dimensionOneDelayScaledPlus dimensionOneRosserSecondSplice)
    (dimensionOneRosserPlusFixedSpliceEndpoint_le hK hL hs hsU hfixed)
  have hshare0 := dimensionOneRosserBoundedSeedShare_pos.le
  calc
    (1 + K * dimensionOneRosserSecondSplice / L) *
          (dimensionOneRosserSeedEnvelope dimensionOneRosserSecondSplice / 2) +
        dimensionOneRosserBoundedSeedShare *
          ((1 - 1 / dimensionOneRosserSecondSplice) *
              (dimensionOneDelayScaledPlus s -
                dimensionOneDelayScaledPlus dimensionOneRosserSecondSplice) +
            (2 * K * dimensionOneRosserSecondSplice /
                (L * (1 - 1 / s))) *
              dimensionOneDelayScaledMinus (s - 1)) <=
        dimensionOneRosserBoundedSeedShare *
            (1 - 1 / dimensionOneRosserSecondSplice) *
              dimensionOneDelayScaledPlus dimensionOneRosserSecondSplice +
          dimensionOneRosserBoundedSeedShare *
            ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) *
                dimensionOneDelayScaledPlus s -
              (1 - 1 / dimensionOneRosserSecondSplice) *
                dimensionOneDelayScaledPlus dimensionOneRosserSecondSplice) :=
      add_le_add hhigh (mul_le_mul_of_nonneg_left hbracket hshare0)
    _ = dimensionOneRosserBoundedSeedShare *
        ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) *
          dimensionOneDelayScaledPlus s) := by ring

/-- The transported high seed and the bounded minus shell fit the retained
minus contraction. -/
theorem dimensionOneRosserMinusFixedSpliceBudget_le
    {K L s : Real} (hK : 0 <= K) (hL : 0 < L)
    (hs : 2 <= s) (hsU : s <= dimensionOneRosserSecondSplice)
    (hfixed :
      48 * K * dimensionOneRosserSecondSplice ^ 2 <=
        L * dimensionOneRosserBoundedDelayFloor) :
    (1 + K * dimensionOneRosserSecondSplice / L) *
          (dimensionOneRosserSeedEnvelope dimensionOneRosserSecondSplice / 2) +
        dimensionOneRosserBoundedSeedShare *
          ((1 - 1 / dimensionOneRosserSecondSplice) *
              (dimensionOneDelayScaledMinus s -
                dimensionOneDelayScaledMinus dimensionOneRosserSecondSplice) +
            (2 * K * dimensionOneRosserSecondSplice /
                (L * (1 - 1 / s))) *
              dimensionOneDelayScaledPlus (s - 1)) <=
      dimensionOneRosserBoundedSeedShare *
        ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) *
          dimensionOneDelayScaledMinus s) := by
  have hterminal := dimensionOneDelayScaledMinus_pos
    (show 0 < dimensionOneRosserSecondSplice by
      linarith [three_lt_dimensionOneRosserSecondSplice])
  have hseed := dimensionOneRosserSeedEnvelope_le_boundedMinus
    (show 2 <= dimensionOneRosserSecondSplice by
      linarith [three_lt_dimensionOneRosserSecondSplice]) le_rfl
  change dimensionOneRosserSeedEnvelope dimensionOneRosserSecondSplice <=
    dimensionOneRosserBoundedSeedShare *
      dimensionOneDelayScaledMinus dimensionOneRosserSecondSplice at hseed
  have hhigh := fixedSpliceSeedTransport_le_terminal hK hL hfixed hseed
    hterminal.le
  have hbracket := fixedSpliceBracket_le
    (current := dimensionOneDelayScaledMinus s)
    (terminal :=
      dimensionOneDelayScaledMinus dimensionOneRosserSecondSplice)
    (dimensionOneRosserMinusFixedSpliceEndpoint_le hK hL hs hsU hfixed)
  have hshare0 := dimensionOneRosserBoundedSeedShare_pos.le
  calc
    (1 + K * dimensionOneRosserSecondSplice / L) *
          (dimensionOneRosserSeedEnvelope dimensionOneRosserSecondSplice / 2) +
        dimensionOneRosserBoundedSeedShare *
          ((1 - 1 / dimensionOneRosserSecondSplice) *
              (dimensionOneDelayScaledMinus s -
                dimensionOneDelayScaledMinus dimensionOneRosserSecondSplice) +
            (2 * K * dimensionOneRosserSecondSplice /
                (L * (1 - 1 / s))) *
              dimensionOneDelayScaledPlus (s - 1)) <=
        dimensionOneRosserBoundedSeedShare *
            (1 - 1 / dimensionOneRosserSecondSplice) *
              dimensionOneDelayScaledMinus dimensionOneRosserSecondSplice +
          dimensionOneRosserBoundedSeedShare *
            ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) *
                dimensionOneDelayScaledMinus s -
              (1 - 1 / dimensionOneRosserSecondSplice) *
                dimensionOneDelayScaledMinus dimensionOneRosserSecondSplice) :=
      add_le_add hhigh (mul_le_mul_of_nonneg_left hbracket hshare0)
    _ = dimensionOneRosserBoundedSeedShare *
        ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) *
          dimensionOneDelayScaledMinus s) := by ring

end PrimesRestrictedDigits
