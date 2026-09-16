import PrimesRestrictedDigits.MajorArcs.LogSubdivision
import PrimesRestrictedDigits.MajorArcs.PositiveBlockScale
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Source growth for positive major-arc blocks

This discharges the sufficiently-large-`X` comparisons suppressed in the
positive-block use of Eq. (5.1) on published pp. 186--188. It proves only
elementary growth and does not assert a prime number theorem.
-/

open Filter Asymptotics

namespace PrimesRestrictedDigits

/-- A PNT exponent chosen uniformly from an outer bound on the source arity. -/
def majorArcPositiveBlockPNTExponent (D ellMax : ℕ) : ℕ :=
  2 * majorArcLogSubdivisionExponent D ellMax + D + 1

/-- The non-sharp growth margins used to discharge both budgets. -/
def majorArcPositiveBlockGrowthConditions
    (X eta Y0 : ℝ) (D ellMax : ℕ) : Prop :=
  Y0 ≤ X ^ (eta / 4) ∧
    (2 * Real.log X) ^ majorArcLogSubdivisionExponent D ellMax ≤
      X ^ (eta / 12) ∧
    (2 * Real.log X) ^
        (2 * majorArcLogSubdivisionExponent D ellMax) *
        Real.log X ^ D ≤
      (eta / 4 * Real.log X) ^
        majorArcPositiveBlockPNTExponent D ellMax ∧
    2 * (2 * Real.log X) ^
        (2 * majorArcLogSubdivisionExponent D ellMax) *
        Real.log X ^ (D + 1) ≤ X ^ (eta / 8)

theorem majorArcPositiveBlockPNTExponent_pos (D ellMax : ℕ) :
    0 < majorArcPositiveBlockPNTExponent D ellMax := by
  dsimp [majorArcPositiveBlockPNTExponent]
  omega

private theorem eventually_const_mul_log_pow_le_rpow
    (C : ℝ) (n : ℕ) {s : ℝ} (hC : 0 ≤ C) (hs : 0 < s) :
    ∀ᶠ x : ℝ in atTop, C * Real.log x ^ n ≤ x ^ s := by
  have hbound :=
    ((isLittleO_log_rpow_rpow_atTop (n : ℝ) hs).const_mul_left C).bound
      zero_lt_one
  filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hleft : 0 ≤ C * Real.log x ^ n :=
    mul_nonneg hC (pow_nonneg hlog n)
  have hright : 0 ≤ x ^ s := Real.rpow_nonneg (by linarith) s
  simpa only [Real.rpow_natCast, Real.norm_of_nonneg hleft,
    Real.norm_of_nonneg hright, one_mul] using hx

theorem eventually_majorArcPositiveBlockGrowthConditions
    (D ellMax : ℕ) {eta Y0 : ℝ}
    (heta : 0 < eta) (hY0 : 0 ≤ Y0) :
    ∀ᶠ X : ℝ in atTop,
      majorArcPositiveBlockGrowthConditions X eta Y0 D ellMax := by
  let B := majorArcLogSubdivisionExponent D ellMax
  let A := majorArcPositiveBlockPNTExponent D ellMax
  have hY0growth := eventually_const_mul_log_pow_le_rpow
    Y0 0 hY0 (by positivity : 0 < eta / 4)
  have hsubdivision := eventually_const_mul_log_pow_le_rpow
    ((2 : ℝ) ^ B) B (by positivity) (by positivity : 0 < eta / 12)
  have hprimePower := eventually_const_mul_log_pow_le_rpow
    ((2 : ℝ) ^ (2 * B + 1)) A (by positivity)
      (by positivity : 0 < eta / 8)
  let C := (2 : ℝ) ^ (2 * B) / (eta / 4) ^ A
  have hcoefficient := Real.tendsto_log_atTop.eventually_ge_atTop C
  filter_upwards [hY0growth, hsubdivision, hprimePower, hcoefficient,
      eventually_gt_atTop (1 : ℝ)] with x hxY0 hxSubdivision hxPrimePower
        hxCoefficient hx1
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have heta4 : 0 < eta / 4 := by positivity
  have hcoefficient' :
      (2 : ℝ) ^ (2 * B) ≤ (eta / 4) ^ A * Real.log x := by
    change (2 : ℝ) ^ (2 * B) / (eta / 4) ^ A ≤
      Real.log x at hxCoefficient
    have h := (div_le_iff₀ (pow_pos heta4 A)).mp hxCoefficient
    nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hxY0
  · simpa [B, mul_pow] using hxSubdivision
  · change (2 * Real.log x) ^ (2 * B) * Real.log x ^ D ≤
      (eta / 4 * Real.log x) ^ A
    rw [mul_pow, mul_pow]
    calc
      2 ^ (2 * B) * Real.log x ^ (2 * B) * Real.log x ^ D =
          Real.log x ^ (2 * B + D) * 2 ^ (2 * B) := by
        rw [pow_add]
        ring
      _ ≤ Real.log x ^ (2 * B + D) *
          ((eta / 4) ^ A * Real.log x) := by gcongr
      _ = (eta / 4) ^ A * Real.log x ^ A := by
        dsimp [A, majorArcPositiveBlockPNTExponent]
        rw [pow_succ]
        ring
  · change 2 * (2 * Real.log x) ^ (2 * B) *
      Real.log x ^ (D + 1) ≤ x ^ (eta / 8)
    rw [mul_pow]
    calc
      2 * (2 ^ (2 * B) * Real.log x ^ (2 * B)) *
          Real.log x ^ (D + 1) =
          2 ^ (2 * B + 1) * Real.log x ^ A := by
        dsimp [A, majorArcPositiveBlockPNTExponent]
        rw [pow_add]
        ring
      _ ≤ x ^ (eta / 8) := hxPrimePower

theorem exists_majorArcPositiveBlockGrowthThreshold
    (D ellMax : ℕ) {eta Y0 : ℝ}
    (heta : 0 < eta) (hY0 : 0 ≤ Y0) :
    ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
      4 ≤ X ∧
        majorArcPositiveBlockGrowthConditions
          (X : ℝ) eta Y0 D ellMax := by
  have hgrowth := eventually_majorArcPositiveBlockGrowthConditions
    D ellMax heta hY0
  have hboth : ∀ᶠ x : ℝ in atTop,
      (4 : ℝ) ≤ x ∧ majorArcPositiveBlockGrowthConditions
        x eta Y0 D ellMax :=
    (eventually_ge_atTop (4 : ℝ)).and hgrowth
  rcases eventually_atTop.mp hboth with ⟨R, hR⟩
  let X0 := Nat.ceil (max R 4)
  refine ⟨X0, ?_⟩
  intro X hX
  have hRX0 : R ≤ (X0 : ℝ) :=
    le_trans (le_max_left R 4) (Nat.le_ceil (max R 4))
  have hX0X : (X0 : ℝ) ≤ X := by exact_mod_cast hX
  have hresult := hR (X : ℝ) (hRX0.trans hX0X)
  exact ⟨by exact_mod_cast hresult.1, hresult.2⟩

private theorem rpow_eta_div_four_lt_majorArcBlockLower
    {X J m j : ℕ} {eta : ℝ} (_heta : 0 < eta) (hX : 4 ≤ X)
    (hJ : 0 < J) (hJpower : (J : ℝ) ≤ (X : ℝ) ^ (eta / 12))
    (hm : 0 < m)
    (hmsupport : (m : ℝ) < (X : ℝ) ^ (1 - eta / 3))
    (hj : 0 < j) :
    (X : ℝ) ^ (eta / 4) <
      majorArcBlockLower (X : ℝ) J m j := by
  let x : ℝ := X
  have hxone : 1 < x := by
    dsimp [x]
    exact_mod_cast (show 1 < X by omega)
  have hxpos : 0 < x := lt_trans (by norm_num) hxone
  have hproduct : (J : ℝ) * (m : ℝ) < x ^ (1 - eta / 4) := by
    calc
      (J : ℝ) * (m : ℝ) ≤ x ^ (eta / 12) * (m : ℝ) := by
        simpa [x] using
          mul_le_mul_of_nonneg_right hJpower (Nat.cast_nonneg m)
      _ < x ^ (eta / 12) * x ^ (1 - eta / 3) := by
        exact mul_lt_mul_of_pos_left (by simpa [x] using hmsupport)
          (Real.rpow_pos_of_pos hxpos _)
      _ = x ^ (1 - eta / 4) := by
        rw [← Real.rpow_add hxpos]
        congr 1
        ring
  have hden : 0 < J * m := Nat.mul_pos hJ hm
  have hdenreal : (0 : ℝ) < (J * m : ℕ) := by exact_mod_cast hden
  have hrpowden : 0 < x ^ (1 - eta / 4) :=
    Real.rpow_pos_of_pos hxpos _
  have hdivision :
      x / x ^ (1 - eta / 4) < x / ((J * m : ℕ) : ℝ) := by
    apply (div_lt_div_iff₀ hrpowden hdenreal).2
    have hproduct' : ((J * m : ℕ) : ℝ) < x ^ (1 - eta / 4) := by
      simpa only [Nat.cast_mul] using hproduct
    exact mul_lt_mul_of_pos_left hproduct' hxpos
  have hquotient : x / x ^ (1 - eta / 4) = x ^ (eta / 4) := by
    calc
      x / x ^ (1 - eta / 4) = x ^ 1 / x ^ (1 - eta / 4) := by
        rw [Real.rpow_one]
      _ = x ^ (1 - (1 - eta / 4)) :=
        (Real.rpow_sub hxpos 1 (1 - eta / 4)).symm
      _ = x ^ (eta / 4) := by congr 1; ring
  have hpowerLength :
      x ^ (eta / 4) < majorArcBlockLength x J m := by
    rw [← hquotient]
    simpa [majorArcBlockLength] using hdivision
  have hlength : 0 < majorArcBlockLength x J m :=
    (Real.rpow_pos_of_pos hxpos _).trans hpowerLength
  calc
    (X : ℝ) ^ (eta / 4) = x ^ (eta / 4) := rfl
    _ < majorArcBlockLength x J m := hpowerLength
    _ ≤ (j : ℝ) * majorArcBlockLength x J m := by
      nlinarith [show (1 : ℝ) ≤ j by exact_mod_cast hj]
    _ = majorArcBlockLower (X : ℝ) J m j := rfl

theorem majorArcPositiveBlock_source_budgets_of_growth
    {X D ell ellMax m j q : ℕ} {eta Y0 : ℝ}
    (heta : 0 < eta) (hY0 : 1 ≤ Y0)
    (_hell : 0 < ell) (hellMax : ell ≤ ellMax)
    (_hellSource : (ell : ℝ) ≤ 2 / eta)
    (hX : 4 ≤ X) (hm : 0 < m)
    (hmsupport : (m : ℝ) < (X : ℝ) ^ (1 - eta / 3))
    (hj : 0 < j)
    (hjJ : j < majorArcLogSubdivisionCount X D ell)
    (_hq : 0 < q) (hqlog : (q : ℝ) ≤ Real.log (X : ℝ) ^ D)
    (hgrowth : majorArcPositiveBlockGrowthConditions
      (X : ℝ) eta Y0 D ellMax) :
    Y0 < majorArcBlockLower (X : ℝ)
        (majorArcLogSubdivisionCount X D ell) m j ∧
      1 < majorArcBlockLower (X : ℝ)
        (majorArcLogSubdivisionCount X D ell) m j ∧
      (majorArcLogSubdivisionCount X D ell : ℝ) ^ 2 * (q : ℝ) ≤
        Real.log (majorArcBlockLower (X : ℝ)
          (majorArcLogSubdivisionCount X D ell) m j) ^
            majorArcPositiveBlockPNTExponent D ellMax ∧
      2 * (majorArcLogSubdivisionCount X D ell : ℝ) ^ 2 *
          (q : ℝ) * Real.log (majorArcBlockUpper (X : ℝ)
            (majorArcLogSubdivisionCount X D ell) m j) ≤
        Real.sqrt (majorArcBlockUpper (X : ℝ)
          (majorArcLogSubdivisionCount X D ell) m j) := by
  let x : ℝ := X
  let J := majorArcLogSubdivisionCount X D ell
  let B := majorArcLogSubdivisionExponent D ellMax
  let A := majorArcPositiveBlockPNTExponent D ellMax
  let Y := majorArcBlockLower x J m j
  let U := majorArcBlockUpper x J m j
  rcases hgrowth with ⟨hY0power, hsubdivision, hraw, hprimePower⟩
  have hxone : 1 < x := by
    dsimp [x]
    exact_mod_cast (show 1 < X by omega)
  have hxpos : 0 < x := lt_trans (by norm_num) hxone
  have hlog : 1 < Real.log x :=
    (Real.lt_log_iff_exp_lt hxpos).mpr <|
      Real.exp_one_lt_three.trans_le (by
        dsimp [x]
        exact_mod_cast (show 3 ≤ X by omega))
  have hbase : 1 ≤ 2 * Real.log x := by linarith
  have hB : majorArcLogSubdivisionExponent D ell ≤ B := by
    dsimp [B, majorArcLogSubdivisionExponent]
    omega
  have hJpoly : (J : ℝ) ≤ (2 * Real.log x) ^ B := by
    calc
      (J : ℝ) ≤
          (2 * Real.log x) ^ majorArcLogSubdivisionExponent D ell := by
        simpa [J, x] using majorArcLogSubdivisionCount_le_two_mul_log_pow
          (D := D) (ell := ell) hX
      _ ≤ (2 * Real.log x) ^ B := pow_le_pow_right₀ hbase hB
  have hJpower : (J : ℝ) ≤ x ^ (eta / 12) :=
    hJpoly.trans (by simpa [x, B] using hsubdivision)
  have hJpos : 0 < J := majorArcLogSubdivisionCount_pos (by omega)
  have hpowerY : x ^ (eta / 4) < Y := by
    simpa [x, J, Y] using rpow_eta_div_four_lt_majorArcBlockLower
      heta hX hJpos hJpower hm hmsupport hj
  have hY0power' : Y0 ≤ x ^ (eta / 4) := by
    simpa [x] using hY0power
  have hY0Y : Y0 < Y := hY0power'.trans_lt hpowerY
  have hYone : 1 < Y := hY0.trans_lt hY0Y
  have hlogY : eta / 4 * Real.log x ≤ Real.log Y := by
    rw [← Real.log_rpow hxpos]
    exact Real.log_le_log (Real.rpow_pos_of_pos hxpos _) hpowerY.le
  have hJ2q : (J : ℝ) ^ 2 * (q : ℝ) ≤
      (2 * Real.log x) ^ (2 * B) * Real.log x ^ D := by
    calc
      (J : ℝ) ^ 2 * (q : ℝ) ≤
          ((2 * Real.log x) ^ B) ^ 2 * Real.log x ^ D := by gcongr
      _ = (2 * Real.log x) ^ (2 * B) * Real.log x ^ D := by
        rw [← pow_mul]
        congr 2
        omega
  have hraw' : (2 * Real.log x) ^ (2 * B) * Real.log x ^ D ≤
      (eta / 4 * Real.log x) ^ A := by
    simpa [x, B, A] using hraw
  have hbudget : (J : ℝ) ^ 2 * (q : ℝ) ≤ Real.log Y ^ A := by
    calc
      _ ≤ (2 * Real.log x) ^ (2 * B) * Real.log x ^ D := hJ2q
      _ ≤ (eta / 4 * Real.log x) ^ A := hraw'
      _ ≤ Real.log Y ^ A :=
        pow_le_pow_left₀ (by positivity) hlogY A
  have hlength : 0 < majorArcBlockLength x J m := by
    rw [majorArcBlockLength]
    positivity
  have hYU : Y ≤ U := by
    dsimp [Y, U, majorArcBlockLower, majorArcBlockUpper]
    apply mul_le_mul_of_nonneg_right _ hlength.le
    exact_mod_cast Nat.le_succ j
  have hUone : 1 < U := hYone.trans_le hYU
  have hUpos : 0 < U := zero_lt_one.trans hUone
  have hUleX : U ≤ x := by
    calc
      U ≤ x / (m : ℝ) := by
        simpa [U, x, J] using majorArcBlockUpper_le_cutoff
          (X := (X : ℝ)) (J := J) (m := m) (j := j)
          (by positivity) hJpos hm hjJ
      _ ≤ x := div_le_self hxpos.le (by exact_mod_cast hm)
  have hlogU : Real.log U ≤ Real.log x :=
    Real.log_le_log hUpos hUleX
  have hlogUnonneg : 0 ≤ Real.log U := Real.log_nonneg hUone.le
  have hphaseSize : 2 * (J : ℝ) ^ 2 * (q : ℝ) * Real.log U ≤
      2 * (2 * Real.log x) ^ (2 * B) * Real.log x ^ (D + 1) := by
    calc
      2 * (J : ℝ) ^ 2 * (q : ℝ) * Real.log U =
          2 * ((J : ℝ) ^ 2 * (q : ℝ)) * Real.log U := by ring
      _ ≤ 2 * ((2 * Real.log x) ^ (2 * B) * Real.log x ^ D) *
          Real.log U := by gcongr
      _ ≤ 2 * ((2 * Real.log x) ^ (2 * B) * Real.log x ^ D) *
          Real.log x := by gcongr
      _ = 2 * (2 * Real.log x) ^ (2 * B) *
          Real.log x ^ (D + 1) := by
        rw [pow_succ]
        ring
  have hprimePower' : 2 * (2 * Real.log x) ^ (2 * B) *
      Real.log x ^ (D + 1) ≤ x ^ (eta / 8) := by
    simpa [x, B] using hprimePower
  have hsqrtPower : x ^ (eta / 8) = Real.sqrt (x ^ (eta / 4)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hxpos.le]
    congr 1
    ring
  have hsqrt : x ^ (eta / 8) ≤ Real.sqrt U := by
    rw [hsqrtPower]
    exact Real.sqrt_le_sqrt (hpowerY.le.trans hYU)
  exact ⟨by simpa [Y], by simpa [Y],
    by simpa [Y, J, A] using hbudget,
    by simpa [U, J] using hphaseSize.trans (hprimePower'.trans hsqrt)⟩

theorem exists_majorArcPositiveBlockSourceBudgetThreshold
    (D ellMax : ℕ) {eta Y0 : ℝ}
    (heta : 0 < eta) (hY0 : 1 ≤ Y0) :
    ∃ X0 : ℕ, ∀ X ell m j q : ℕ,
      X0 ≤ X → 0 < ell → ell ≤ ellMax →
      (ell : ℝ) ≤ 2 / eta → 0 < m →
      (m : ℝ) < (X : ℝ) ^ (1 - eta / 3) →
      0 < j → j < majorArcLogSubdivisionCount X D ell →
      0 < q → (q : ℝ) ≤ Real.log (X : ℝ) ^ D →
      Y0 < majorArcBlockLower (X : ℝ)
          (majorArcLogSubdivisionCount X D ell) m j ∧
        1 < majorArcBlockLower (X : ℝ)
          (majorArcLogSubdivisionCount X D ell) m j ∧
        (majorArcLogSubdivisionCount X D ell : ℝ) ^ 2 * (q : ℝ) ≤
          Real.log (majorArcBlockLower (X : ℝ)
            (majorArcLogSubdivisionCount X D ell) m j) ^
              majorArcPositiveBlockPNTExponent D ellMax ∧
        2 * (majorArcLogSubdivisionCount X D ell : ℝ) ^ 2 *
            (q : ℝ) * Real.log (majorArcBlockUpper (X : ℝ)
              (majorArcLogSubdivisionCount X D ell) m j) ≤
          Real.sqrt (majorArcBlockUpper (X : ℝ)
            (majorArcLogSubdivisionCount X D ell) m j) := by
  have hY0nonneg : 0 ≤ Y0 := zero_le_one.trans hY0
  rcases exists_majorArcPositiveBlockGrowthThreshold
    D ellMax heta hY0nonneg with ⟨X0, hX0⟩
  refine ⟨X0, ?_⟩
  intro X ell m j q hthreshold hell hellMax hellSource hm hmsupport
    hj hjJ hq hqlog
  rcases hX0 X hthreshold with ⟨hX, hgrowth⟩
  exact majorArcPositiveBlock_source_budgets_of_growth
    heta hY0 hell hellMax hellSource hX hm hmsupport hj hjJ hq hqlog hgrowth

end PrimesRestrictedDigits
