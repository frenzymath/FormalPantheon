import Waring.Analytic.ChenNineProductScale

/-!
# Corrected back-substitution in Chen's Lemma 9

This file propagates the direct product aggregate through the three valid
differencing inequalities.  Trivial bounds absorb only the non-leading
binomial terms.
-/

namespace Waring.Analytic

/-- The corrected third differencing step raises the aggregate coefficient
from `160` to `160+1/5`. -/
theorem chenNine_fourthPower_backSubstitution
    (p A S F : Real) (hp : 1 ≤ p)
    (hF : 8 ≤ F) (hStrivial : S ≤ p ^ 4)
    (hS : S ^ 2 ≤ 160 * p ^ 7 * F)
    (hA : 2 * A ^ 2 ≤ p ^ 5 + 2 * p ^ 2 * S) :
    A ^ 4 ≤ (801 / 5 : Real) * p ^ 11 * F := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hsq := pow_le_pow_left₀ (mul_nonneg (by norm_num) (sq_nonneg A)) hA 2
  have hpTenEleven : p ^ 10 ≤ p ^ 11 := by
    calc
      p ^ 10 ≤ p ^ 10 * p :=
        by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hp (pow_nonneg hp0 10)
      _ = p ^ 11 := by ring
  have hcross : 4 * p ^ 7 * S ≤ 4 * p ^ 11 := by
    calc
      4 * p ^ 7 * S ≤ 4 * p ^ 7 * p ^ 4 := by gcongr
      _ = 4 * p ^ 11 := by ring
  have hextra : p ^ 10 + 4 * p ^ 7 * S ≤ 5 * p ^ 11 := by
    linarith
  have hmain : 4 * p ^ 4 * S ^ 2 ≤ 640 * p ^ 11 * F := by
    calc
      4 * p ^ 4 * S ^ 2 ≤ 4 * p ^ 4 * (160 * p ^ 7 * F) := by
        gcongr
      _ = 640 * p ^ 11 * F := by ring
  have hslack : 5 * p ^ 11 ≤ (4 / 5 : Real) * p ^ 11 * F := by
    have hmul := mul_le_mul_of_nonneg_left hF (pow_nonneg hp0 11)
    nlinarith
  have hfour : 4 * A ^ 4 ≤ 4 * ((801 / 5 : Real) * p ^ 11 * F) := by
    calc
      4 * A ^ 4 = (2 * A ^ 2) ^ 2 := by ring
      _ ≤ (p ^ 5 + 2 * p ^ 2 * S) ^ 2 := hsq
      _ = (p ^ 10 + 4 * p ^ 7 * S) + 4 * p ^ 4 * S ^ 2 := by ring
      _ ≤ 5 * p ^ 11 + 640 * p ^ 11 * F :=
        add_le_add hextra hmain
      _ ≤ (4 / 5 : Real) * p ^ 11 * F + 640 * p ^ 11 * F :=
        add_le_add hslack le_rfl
      _ = 4 * ((801 / 5 : Real) * p ^ 11 * F) := by ring
  nlinarith

/-- The second differencing step raises `160+1/5` to `160+1/3` and
contributes the leading factor `16`. -/
theorem chenNine_eighthPower_backSubstitution
    (p A B F : Real) (hp : 1 ≤ p) (hA0 : 0 ≤ A)
    (hF : 64 ≤ F) (hAtrivial : A ≤ p ^ 3)
    (hA : A ^ 4 ≤ (801 / 5 : Real) * p ^ 11 * F)
    (hB : B ^ 2 ≤ p ^ 3 + 2 * p * A) :
    B ^ 8 ≤ 16 * (481 / 3 : Real) * p ^ 15 * F := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hpow := pow_le_pow_left₀ (sq_nonneg B) hB 4
  have hA2 : A ^ 2 ≤ (p ^ 3) ^ 2 :=
    pow_le_pow_left₀ hA0 hAtrivial 2
  have hA3 : A ^ 3 ≤ (p ^ 3) ^ 3 :=
    pow_le_pow_left₀ hA0 hAtrivial 3
  have hp12 : p ^ 12 ≤ p ^ 15 := pow_le_pow_right₀ hp (by norm_num)
  have hterm1 : 8 * p ^ 10 * A ≤ 8 * p ^ 15 := by
    calc
      8 * p ^ 10 * A ≤ 8 * p ^ 10 * p ^ 3 := by gcongr
      _ = 8 * p ^ 13 := by ring
      _ ≤ 8 * p ^ 15 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hp (by norm_num)) (by norm_num)
  have hterm2 : 24 * p ^ 8 * A ^ 2 ≤ 24 * p ^ 15 := by
    calc
      24 * p ^ 8 * A ^ 2 ≤ 24 * p ^ 8 * (p ^ 3) ^ 2 := by gcongr
      _ = 24 * p ^ 14 := by ring
      _ ≤ 24 * p ^ 15 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hp (by norm_num)) (by norm_num)
  have hterm3 : 32 * p ^ 6 * A ^ 3 ≤ 32 * p ^ 15 := by
    calc
      32 * p ^ 6 * A ^ 3 ≤ 32 * p ^ 6 * (p ^ 3) ^ 3 := by gcongr
      _ = 32 * p ^ 15 := by ring
  have hcross : p ^ 12 + 8 * p ^ 10 * A + 24 * p ^ 8 * A ^ 2 +
      32 * p ^ 6 * A ^ 3 ≤ 65 * p ^ 15 := by
    linarith
  have hmain : 16 * p ^ 4 * A ^ 4 ≤
      16 * (801 / 5 : Real) * p ^ 15 * F := by
    calc
      16 * p ^ 4 * A ^ 4 ≤
          16 * p ^ 4 * ((801 / 5 : Real) * p ^ 11 * F) := by gcongr
      _ = 16 * (801 / 5 : Real) * p ^ 15 * F := by ring
  have hslack : 65 * p ^ 15 ≤ (32 / 15 : Real) * p ^ 15 * F := by
    have hmul := mul_le_mul_of_nonneg_left hF (pow_nonneg hp0 15)
    nlinarith
  calc
    B ^ 8 = (B ^ 2) ^ 4 := by ring
    _ ≤ (p ^ 3 + 2 * p * A) ^ 4 := hpow
    _ = (p ^ 12 + 8 * p ^ 10 * A + 24 * p ^ 8 * A ^ 2 +
        32 * p ^ 6 * A ^ 3) + 16 * p ^ 4 * A ^ 4 := by ring
    _ ≤ 65 * p ^ 15 + 16 * (801 / 5 : Real) * p ^ 15 * F :=
      add_le_add hcross hmain
    _ ≤ (32 / 15 : Real) * p ^ 15 * F +
        16 * (801 / 5 : Real) * p ^ 15 * F :=
      add_le_add hslack le_rfl
    _ = 16 * (481 / 3 : Real) * p ^ 15 * F := by ring

/-- The first differencing step absorbs its seven non-leading binomial terms
and rounds the final coefficient to `161`. -/
theorem chenNine_sixteenthPower_backSubstitution
    (p B T F u : Real) (hp : 1 ≤ p) (hB0 : 0 ≤ B)
    (hF : 64 ≤ F) (hu : 1 ≤ u) (hBtrivial : B ≤ p ^ 2)
    (hB : B ^ 8 ≤ 16 * (481 / 3 : Real) * p ^ 15 * F)
    (hT : T ^ 2 ≤ p + 2 * B) :
    T ^ 16 ≤ 2 ^ 12 * 161 * p ^ 15 * F * u := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hpow := pow_le_pow_left₀ (sq_nonneg T) hT 8
  have hB2 := pow_le_pow_left₀ hB0 hBtrivial 2
  have hB3 := pow_le_pow_left₀ hB0 hBtrivial 3
  have hB4 := pow_le_pow_left₀ hB0 hBtrivial 4
  have hB5 := pow_le_pow_left₀ hB0 hBtrivial 5
  have hB6 := pow_le_pow_left₀ hB0 hBtrivial 6
  have hB7 := pow_le_pow_left₀ hB0 hBtrivial 7
  have hp8 : p ^ 8 ≤ p ^ 15 := pow_le_pow_right₀ hp (by norm_num)
  have hterm1 : 16 * p ^ 7 * B ≤ 16 * p ^ 15 := by
    calc
      16 * p ^ 7 * B ≤ 16 * p ^ 7 * p ^ 2 := by gcongr
      _ = 16 * p ^ 9 := by ring
      _ ≤ 16 * p ^ 15 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hp (by norm_num)) (by norm_num)
  have hterm2 : 112 * p ^ 6 * B ^ 2 ≤ 112 * p ^ 15 := by
    calc
      112 * p ^ 6 * B ^ 2 ≤ 112 * p ^ 6 * (p ^ 2) ^ 2 := by gcongr
      _ = 112 * p ^ 10 := by ring
      _ ≤ 112 * p ^ 15 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hp (by norm_num)) (by norm_num)
  have hterm3 : 448 * p ^ 5 * B ^ 3 ≤ 448 * p ^ 15 := by
    calc
      448 * p ^ 5 * B ^ 3 ≤ 448 * p ^ 5 * (p ^ 2) ^ 3 := by gcongr
      _ = 448 * p ^ 11 := by ring
      _ ≤ 448 * p ^ 15 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hp (by norm_num)) (by norm_num)
  have hterm4 : 1120 * p ^ 4 * B ^ 4 ≤ 1120 * p ^ 15 := by
    calc
      1120 * p ^ 4 * B ^ 4 ≤ 1120 * p ^ 4 * (p ^ 2) ^ 4 := by gcongr
      _ = 1120 * p ^ 12 := by ring
      _ ≤ 1120 * p ^ 15 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hp (by norm_num)) (by norm_num)
  have hterm5 : 1792 * p ^ 3 * B ^ 5 ≤ 1792 * p ^ 15 := by
    calc
      1792 * p ^ 3 * B ^ 5 ≤ 1792 * p ^ 3 * (p ^ 2) ^ 5 := by gcongr
      _ = 1792 * p ^ 13 := by ring
      _ ≤ 1792 * p ^ 15 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hp (by norm_num)) (by norm_num)
  have hterm6 : 1792 * p ^ 2 * B ^ 6 ≤ 1792 * p ^ 15 := by
    calc
      1792 * p ^ 2 * B ^ 6 ≤ 1792 * p ^ 2 * (p ^ 2) ^ 6 := by gcongr
      _ = 1792 * p ^ 14 := by ring
      _ ≤ 1792 * p ^ 15 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hp (by norm_num)) (by norm_num)
  have hterm7 : 1024 * p * B ^ 7 ≤ 1024 * p ^ 15 := by
    calc
      1024 * p * B ^ 7 ≤ 1024 * p * (p ^ 2) ^ 7 := by gcongr
      _ = 1024 * p ^ 15 := by ring
  have hcross : p ^ 8 + 16 * p ^ 7 * B + 112 * p ^ 6 * B ^ 2 +
      448 * p ^ 5 * B ^ 3 + 1120 * p ^ 4 * B ^ 4 +
      1792 * p ^ 3 * B ^ 5 + 1792 * p ^ 2 * B ^ 6 +
      1024 * p * B ^ 7 ≤ 6305 * p ^ 15 := by
    linarith
  have hmain : 256 * B ^ 8 ≤
      4096 * (481 / 3 : Real) * p ^ 15 * F := by
    nlinarith
  have hslack : 6305 * p ^ 15 ≤ (8192 / 3 : Real) * p ^ 15 * F := by
    have hmul := mul_le_mul_of_nonneg_left hF (pow_nonneg hp0 15)
    nlinarith
  have hwithoutU : T ^ 16 ≤ 4096 * 161 * p ^ 15 * F := by
    calc
      T ^ 16 = (T ^ 2) ^ 8 := by ring
      _ ≤ (p + 2 * B) ^ 8 := hpow
      _ = (p ^ 8 + 16 * p ^ 7 * B + 112 * p ^ 6 * B ^ 2 +
          448 * p ^ 5 * B ^ 3 + 1120 * p ^ 4 * B ^ 4 +
          1792 * p ^ 3 * B ^ 5 + 1792 * p ^ 2 * B ^ 6 +
          1024 * p * B ^ 7) + 256 * B ^ 8 := by ring
      _ ≤ 6305 * p ^ 15 +
          4096 * (481 / 3 : Real) * p ^ 15 * F :=
        add_le_add hcross hmain
      _ ≤ (8192 / 3 : Real) * p ^ 15 * F +
          4096 * (481 / 3 : Real) * p ^ 15 * F :=
        add_le_add hslack le_rfl
      _ = 4096 * 161 * p ^ 15 * F := by ring
  calc
    T ^ 16 ≤ 4096 * 161 * p ^ 15 * F := hwithoutU
    _ ≤ 4096 * 161 * p ^ 15 * F * u := by
      exact le_mul_of_one_le_right (by positivity) hu
    _ = 2 ^ 12 * 161 * p ^ 15 * F * u := by norm_num

/-- The fifth-root factor used in all diagonal absorptions is already at
least `64`. -/
theorem sixtyFour_le_chenNineBackSubFactor {P : Nat} (hP : 1 ≤ P) :
    (64 : Real) ≤ chenNineLengthRoot P * chenNineLogRoot P ^ 74 := by
  have hLengthOne : (1 : Real) ≤ chenNineLengthRoot P := by
    unfold chenNineLengthRoot
    exact Real.one_le_rpow (by exact_mod_cast hP) (by norm_num)
  have hLogPow := chenNineLogRoot_pow_five hP
  have hLogOne : (1 : Real) ≤ chenNineLogRoot P := by
    unfold chenNineLogRoot
    have hbase : (1 : Real) ≤ Real.log P + 4 := by
      have hlog : 0 ≤ Real.log P :=
        Real.log_nonneg (by exact_mod_cast hP)
      linarith
    exact Real.one_le_rpow hbase (by norm_num)
  have hLogFifteen : (64 : Real) ≤ chenNineLogRoot P ^ 15 := by
    rw [show chenNineLogRoot P ^ 15 =
      (chenNineLogRoot P ^ 5) ^ 3 by ring, hLogPow]
    have hbase : (4 : Real) ≤ Real.log P + 4 := by
      have hlog : 0 ≤ Real.log P :=
        Real.log_nonneg (by exact_mod_cast hP)
      linarith
    calc
      (64 : Real) = 4 ^ 3 := by norm_num
      _ ≤ (Real.log P + 4) ^ 3 :=
        pow_le_pow_left₀ (by norm_num) hbase 3
  have hLogSeventyFour : chenNineLogRoot P ^ 15 ≤
      chenNineLogRoot P ^ 74 :=
    pow_le_pow_right₀ hLogOne (by norm_num)
  calc
    (64 : Real) ≤ chenNineLogRoot P ^ 15 := hLogFifteen
    _ ≤ chenNineLogRoot P ^ 74 := hLogSeventyFour
    _ = 1 * chenNineLogRoot P ^ 74 := by ring
    _ ≤ chenNineLengthRoot P * chenNineLogRoot P ^ 74 := by
      exact mul_le_mul_of_nonneg_right hLengthOne
        (pow_nonneg (chenNineLogRoot_pos hP).le 74)

/-- The three valid differencing inequalities and their trivial range bounds
imply the corrected rational-phase estimate with coefficient `161`. -/
theorem chenNine_corrected_backSubstitution
    {P : Nat} (T B A S : Real) (hP : 10 ^ 150 ≤ P)
    (hB0 : 0 ≤ B) (hA0 : 0 ≤ A)
    (hBtrivial : B ≤ (P : Real) ^ 2)
    (hAtrivial : A ≤ (P : Real) ^ 3)
    (hStrivial : S ≤ (P : Real) ^ 4)
    (hT : T ^ 2 ≤ P + 2 * B)
    (hB : B ^ 2 ≤ (P : Real) ^ 3 + 2 * P * A)
    (hA : 2 * A ^ 2 ≤ (P : Real) ^ 5 + 2 * (P : Real) ^ 2 * S)
    (hS : S ^ 2 ≤ 160 * (P : Real) ^ (36 / 5 : Real) *
      (Real.log P + 4) ^ (74 / 5 : Real)) :
    T ≤ (2 : Real) ^ (6 / 8 : Real) * (161 : Real) ^ (1 / 16 : Real) *
      (P : Real) ^ (19 / 20 : Real) *
        (Real.log P + 4) ^ (15 / 16 : Real) := by
  let p : Real := P
  let u := chenNineLogRoot P
  let F := chenNineLengthRoot P * u ^ 74
  have hPoneNat : 1 ≤ P :=
    (by norm_num : 1 ≤ (10 : Nat) ^ 150).trans hP
  have hp : (1 : Real) ≤ p := by
    dsimp [p]
    exact_mod_cast hPoneNat
  have hpPos : 0 < p := zero_lt_one.trans_le hp
  have hu : (1 : Real) ≤ u := by
    dsimp [u, chenNineLogRoot]
    have hbase : (1 : Real) ≤ Real.log P + 4 := by
      have hlog : 0 ≤ Real.log P :=
        Real.log_nonneg (by exact_mod_cast hPoneNat)
      linarith
    exact Real.one_le_rpow hbase (by norm_num)
  have hF : (64 : Real) ≤ F :=
    sixtyFour_le_chenNineBackSubFactor hPoneNat
  have hpThirtySix : (P : Real) ^ (36 / 5 : Real) =
      (P : Real) ^ 7 * chenNineLengthRoot P := by
    unfold chenNineLengthRoot
    calc
      (P : Real) ^ (36 / 5 : Real) =
          (P : Real) ^ ((7 : Real) + 1 / 5) := by norm_num
      _ = (P : Real) ^ (7 : Real) * (P : Real) ^ (1 / 5 : Real) := by
        rw [Real.rpow_add (by exact_mod_cast hPoneNat : (0 : Real) < P)]
      _ = (P : Real) ^ 7 * (P : Real) ^ (1 / 5 : Real) := by
        norm_num [Real.rpow_natCast]
  have hlogSeventyFour : (Real.log P + 4) ^ (74 / 5 : Real) =
      chenNineLogRoot P ^ 74 := by
    symm
    unfold chenNineLogRoot
    have hbase : 0 ≤ Real.log P + 4 := by
      have hlog : 0 ≤ Real.log P :=
        Real.log_nonneg (by exact_mod_cast hPoneNat)
      linarith
    rw [← Real.rpow_mul_natCast hbase]
    norm_num
  have hSroot : S ^ 2 ≤ 160 * p ^ 7 * F := by
    calc
      S ^ 2 ≤ 160 * (P : Real) ^ (36 / 5 : Real) *
          (Real.log P + 4) ^ (74 / 5 : Real) := hS
      _ = 160 * p ^ 7 * F := by
        rw [hpThirtySix, hlogSeventyFour]
        dsimp [p, F, u]
        ring
  have hAfour := chenNine_fourthPower_backSubstitution p A S F hp
    ((by norm_num : (8 : Real) ≤ 64).trans hF) hStrivial hSroot hA
  have hBeight := chenNine_eighthPower_backSubstitution p A B F hp hA0
    hF hAtrivial hAfour hB
  have hTsixteen := chenNine_sixteenthPower_backSubstitution p B T F u hp
    hB0 hF hu hBtrivial hBeight hT
  have hpSeventySix : p ^ 15 * chenNineLengthRoot P =
      (P : Real) ^ (76 / 5 : Real) := by
    dsimp [p]
    unfold chenNineLengthRoot
    calc
      (P : Real) ^ 15 * (P : Real) ^ (1 / 5 : Real) =
          (P : Real) ^ (15 : Real) * (P : Real) ^ (1 / 5 : Real) := by
        norm_num [Real.rpow_natCast]
      _ = (P : Real) ^ ((15 : Real) + 1 / 5) := by
        rw [← Real.rpow_add (by exact_mod_cast hPoneNat : (0 : Real) < P)]
      _ = (P : Real) ^ (76 / 5 : Real) := by norm_num
  have hLogPow := chenNineLogRoot_pow_five hPoneNat
  have hrootScale : p ^ 15 * F * u =
      (P : Real) ^ (76 / 5 : Real) * (Real.log P + 4) ^ 15 := by
    dsimp [F, u]
    calc
      p ^ 15 * (chenNineLengthRoot P * chenNineLogRoot P ^ 74) *
          chenNineLogRoot P =
          (p ^ 15 * chenNineLengthRoot P) *
            (chenNineLogRoot P ^ 74 * chenNineLogRoot P) := by ring
      _ = (P : Real) ^ (76 / 5 : Real) * chenNineLogRoot P ^ 75 := by
        rw [hpSeventySix]
        congr 1
      _ = (P : Real) ^ (76 / 5 : Real) *
          (Real.log P + 4) ^ 15 := by
        rw [show chenNineLogRoot P ^ 75 =
          (chenNineLogRoot P ^ 5) ^ 15 by ring, hLogPow]
  have hTsixteen' : T ^ 16 ≤
      2 ^ 12 * 161 * (P : Real) ^ (76 / 5 : Real) *
        (Real.log P + 4) ^ 15 := by
    calc
      T ^ 16 ≤ 2 ^ 12 * 161 * p ^ 15 * F * u := hTsixteen
      _ = 2 ^ 12 * 161 * (p ^ 15 * F * u) := by ring
      _ = 2 ^ 12 * 161 * (P : Real) ^ (76 / 5 : Real) *
          (Real.log P + 4) ^ 15 := by rw [hrootScale]; ring
  let target : Real :=
    (2 : Real) ^ (6 / 8 : Real) * (161 : Real) ^ (1 / 16 : Real) *
      (P : Real) ^ (19 / 20 : Real) *
        (Real.log P + 4) ^ (15 / 16 : Real)
  have hlogBase : 0 ≤ Real.log P + 4 := by
    have hlog : 0 ≤ Real.log P :=
      Real.log_nonneg (by exact_mod_cast hPoneNat)
    linarith
  have htarget0 : 0 ≤ target := by
    dsimp [target]
    positivity
  have htargetPow : target ^ 16 =
      2 ^ 12 * 161 * (P : Real) ^ (76 / 5 : Real) *
        (Real.log P + 4) ^ 15 := by
    dsimp [target]
    calc
      ((2 : Real) ^ (6 / 8 : Real) * (161 : Real) ^ (1 / 16 : Real) *
          (P : Real) ^ (19 / 20 : Real) *
          (Real.log P + 4) ^ (15 / 16 : Real)) ^ 16 =
          ((2 : Real) ^ (6 / 8 : Real)) ^ 16 *
          ((161 : Real) ^ (1 / 16 : Real)) ^ 16 *
          ((P : Real) ^ (19 / 20 : Real)) ^ 16 *
          ((Real.log P + 4) ^ (15 / 16 : Real)) ^ 16 := by ring
      _ = 2 ^ 12 * 161 * (P : Real) ^ (76 / 5 : Real) *
          (Real.log P + 4) ^ 15 := by
        rw [← Real.rpow_mul_natCast (by norm_num : (0 : Real) ≤ 2)]
        rw [← Real.rpow_mul_natCast (by norm_num : (0 : Real) ≤ 161)]
        rw [← Real.rpow_mul_natCast
          (by positivity : (0 : Real) ≤ (P : Real))]
        rw [← Real.rpow_mul_natCast hlogBase]
        norm_num [Real.rpow_natCast]
  change T ≤ target
  apply le_of_pow_le_pow_left₀ (by norm_num : (16 : Nat) ≠ 0) htarget0
  rw [htargetPow]
  exact hTsixteen'

end Waring.Analytic
