import PrimesRestrictedDigits.MajorArcs.M2Contribution
import PrimesRestrictedDigits.MajorArcs.LogSubdivision
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Logarithmic absorption for the M2 estimate

This specializes the repaired finite estimate from `M2Contribution` to the
logarithmic width on pp. 187--188 of `MAYNARD-PRD-PUBLISHED`. The local prime
distribution estimate remains outside this elementary growth module.
-/

open Filter Asymptotics

namespace PrimesRestrictedDigits

/-- Maynard's varying box width `1 / log (log X)`. -/
noncomputable def majorArcM2LogLogDelta (X : Nat) : Real :=
  (Real.log (Real.log (X : Real)))⁻¹

/-- The exact coefficient after inserting the logarithmic subdivision. -/
noncomputable def majorArcM2LogScaleCoefficient
    (X D k : Nat) (eta E : Real) (c : Int) : Real :=
  (Real.log 4 * majorArcM2RelaxationScale (X : Real)
        (majorArcM2LogLogDelta X) eta +
      (E + 1 + 2 * Real.pi * |(c : Real)| * Real.log 4 + Real.log 4) *
        majorArcSubdivisionWidth
          (majorArcLogSubdivisionCount X D (k + 1)) * (X : Real)) *
    (2 * Real.log 4 * Real.log (X : Real)) ^ k

private theorem eventually_const_mul_log_pow_le_rpow
    (C : Real) (n : Nat) {s : Real} (hC : 0 ≤ C) (hs : 0 < s) :
    ∀ᶠ x : Real in atTop, C * Real.log x ^ n ≤ x ^ s := by
  have hbound :=
    ((isLittleO_log_rpow_rpow_atTop (n : Real) hs).const_mul_left C).bound
      zero_lt_one
  filter_upwards [hbound, eventually_ge_atTop (1 : Real)] with x hx hx1
  have hleft : 0 ≤ C * Real.log x ^ n :=
    mul_nonneg hC (pow_nonneg (Real.log_nonneg hx1) n)
  have hright : 0 ≤ x ^ s := Real.rpow_nonneg (by linarith) s
  simpa only [Real.rpow_natCast, Real.norm_of_nonneg hleft,
    Real.norm_of_nonneg hright, one_mul] using hx

private theorem eventually_const_mul_pow_le_exp_div_log
    (C : Real) (n : Nat) :
    ∀ᶠ y : Real in atTop, C * y ^ n ≤ Real.exp (y / Real.log y) := by
  have hsmall :=
    (Real.isLittleO_pow_log_id_atTop (n := 2)).bound
      (show 0 < ((n + 1 : Nat) : Real)⁻¹ by positivity)
  filter_upwards [hsmall,
      eventually_ge_atTop (max C (Real.exp 1))] with y hy hlarge
  have hyExp : Real.exp 1 ≤ y :=
    (le_max_right C (Real.exp 1)).trans hlarge
  have hyOne : 1 < y := (Real.one_lt_exp_iff.mpr one_pos).trans_le hyExp
  have hyPos : 0 < y := zero_lt_one.trans hyOne
  have hlogPos : 0 < Real.log y := Real.log_pos hyOne
  have hCyle : C * y ^ n ≤ y ^ (n + 1) := by
    rw [pow_succ]
    simpa [mul_comm] using mul_le_mul_of_nonneg_right
      ((le_max_left C (Real.exp 1)).trans hlarge) (pow_nonneg hyPos.le n)
  have hsquare : ((n + 1 : Nat) : Real) * Real.log y ^ 2 ≤ y := by
    have hy' : Real.log y ^ 2 ≤ ((n + 1 : Nat) : Real)⁻¹ * y := by
      simpa [Function.id_def, Real.norm_of_nonneg (sq_nonneg _),
        Real.norm_of_nonneg hyPos.le] using hy
    have hnPos : (0 : Real) < (n + 1 : Nat) := by positivity
    calc
      ((n + 1 : Nat) : Real) * Real.log y ^ 2 ≤
          ((n + 1 : Nat) : Real) *
            (((n + 1 : Nat) : Real)⁻¹ * y) :=
        mul_le_mul_of_nonneg_left hy' hnPos.le
      _ = y := by field_simp
  have hexponent :
      ((n + 1 : Nat) : Real) * Real.log y ≤ y / Real.log y :=
    (le_div_iff₀ hlogPos).2 (by simpa [pow_two, mul_assoc] using hsquare)
  calc
    C * y ^ n ≤ y ^ (n + 1) := hCyle
    _ = Real.exp (((n + 1 : Nat) : Real) * Real.log y) := by
      rw [Real.exp_nat_mul, Real.exp_log hyPos]
    _ ≤ Real.exp (y / Real.log y) := Real.exp_le_exp.mpr hexponent

private theorem eventually_const_mul_log_pow_le_rpow_inv_log_log
    (C : Real) (n : Nat) :
    ∀ᶠ x : Real in atTop,
      C * Real.log x ^ n ≤ x ^ (Real.log (Real.log x))⁻¹ := by
  have hbase := eventually_const_mul_pow_le_exp_div_log C n
  have hpull := Real.tendsto_log_atTop.eventually hbase
  filter_upwards [hpull, eventually_gt_atTop (Real.exp 1)] with x hx hxlarge
  have hxPos : 0 < x := (Real.exp_pos 1).trans hxlarge
  rw [Real.rpow_def_of_pos hxPos]
  simpa [div_eq_mul_inv] using hx

private theorem majorArcM2RelaxationTerm_le
    {x L s : Real} {k R D : Nat}
    (hx : 0 < x) (hL : 1 ≤ L) (hk : k ≤ R)
    (hC0 : 1 ≤ 2 * Real.log 4)
    (hbound : Real.log 4 * (2 * Real.log 4) ^ R * L ^ (R + 4 * D) ≤
      x ^ s) :
    Real.log 4 * x ^ (1 - s) * (2 * Real.log 4 * L) ^ k ≤
      x / L ^ (4 * D) := by
  have hlogFour : 0 ≤ Real.log 4 := (Real.log_pos (by norm_num)).le
  have hprefix :
      Real.log 4 * (2 * Real.log 4) ^ k * L ^ (k + 4 * D) ≤ x ^ s := by
    calc
      Real.log 4 * (2 * Real.log 4) ^ k * L ^ (k + 4 * D) ≤
          Real.log 4 * (2 * Real.log 4) ^ R * L ^ (R + 4 * D) := by
        gcongr
      _ ≤ x ^ s := hbound
  have hden : 0 < L ^ (4 * D) := pow_pos (zero_lt_one.trans_le hL) _
  rw [le_div_iff₀ hden]
  calc
    (Real.log 4 * x ^ (1 - s) * (2 * Real.log 4 * L) ^ k) *
          L ^ (4 * D) =
        (Real.log 4 * (2 * Real.log 4) ^ k * L ^ (k + 4 * D)) *
          x ^ (1 - s) := by
      rw [mul_pow, pow_add]
      ring
    _ ≤ x ^ s * x ^ (1 - s) := by gcongr
    _ = x := by
      rw [← Real.rpow_add hx,
        show s + (1 - s) = 1 by ring, Real.rpow_one]

private theorem majorArcM2BlockTerm_le
    {X D k R : Nat} {E : Real} {c : Int}
    (hX : 4 ≤ X) (hk : k ≤ R) (hE : 0 ≤ E)
    (hc : |(c : Real)| ≤ Real.log (X : Real) ^ D)
    (hbound :
      (E + 1 + 2 * Real.pi * Real.log 4 + Real.log 4) *
          (2 * Real.log 4) ^ R ≤
        Real.log (X : Real) ^ (5 * D + 10)) :
    (E + 1 + 2 * Real.pi * |(c : Real)| * Real.log 4 + Real.log 4) *
        majorArcSubdivisionWidth
          (majorArcLogSubdivisionCount X D (k + 1)) * (X : Real) *
        (2 * Real.log 4 * Real.log (X : Real)) ^ k ≤
      (X : Real) / Real.log (X : Real) ^ (4 * D) := by
  let x : Real := X
  let L := Real.log x
  let C0 := 2 * Real.log 4
  let B := (E + 1 + 2 * Real.pi * Real.log 4 + Real.log 4) * C0 ^ R
  let N := majorArcLogSubdivisionExponent D (k + 1)
  have hL : 1 < L := by
    dsimp [L, x]
    exact (Real.lt_log_iff_exp_lt (by positivity)).mpr <|
      Real.exp_one_lt_three.trans_le (by exact_mod_cast (show 3 ≤ X by omega))
  have hC0 : 1 ≤ C0 := by
    dsimp [C0]
    have : (1 : Real) < Real.log 4 :=
      (Real.lt_log_iff_exp_lt (by norm_num)).2
        (Real.exp_one_lt_three.trans_le (by norm_num))
    linarith
  have hLD : 1 ≤ L ^ D := one_le_pow₀ hL.le
  have hcoefficient :
      E + 1 + 2 * Real.pi * |(c : Real)| * Real.log 4 + Real.log 4 ≤
        (E + 1 + 2 * Real.pi * Real.log 4 + Real.log 4) * L ^ D := by
    have hfixed : 0 ≤ E + 1 + Real.log 4 := by positivity
    have hfixedLe :
        E + 1 + Real.log 4 ≤ (E + 1 + Real.log 4) * L ^ D := by
      nlinarith [mul_le_mul_of_nonneg_left hLD hfixed]
    have hphase :
        2 * Real.pi * |(c : Real)| * Real.log 4 ≤
          2 * Real.pi * L ^ D * Real.log 4 := by gcongr
    nlinarith
  have hprefix :
      (E + 1 + 2 * Real.pi * |(c : Real)| * Real.log 4 + Real.log 4) *
          (C0 * L) ^ k ≤ B * L ^ (D + k) := by
    calc
      _ ≤ ((E + 1 + 2 * Real.pi * Real.log 4 + Real.log 4) * L ^ D) *
          (C0 * L) ^ k := by gcongr
      _ ≤ ((E + 1 + 2 * Real.pi * Real.log 4 + Real.log 4) * L ^ D) *
          (C0 ^ R * L ^ k) := by
        rw [mul_pow]
        gcongr
      _ = B * L ^ (D + k) := by
        dsimp [B]
        rw [pow_add]
        ring
  have hwidth :
      majorArcSubdivisionWidth
          (majorArcLogSubdivisionCount X D (k + 1)) ≤ (L ^ N)⁻¹ := by
    simpa [L, x, N] using
      majorArcLogSubdivisionWidth_le_inv_log_pow
        (D := D) (ell := k + 1) (show 1 < X by omega)
  have hwidthNonneg :
      0 ≤ majorArcSubdivisionWidth
        (majorArcLogSubdivisionCount X D (k + 1)) := by
    dsimp [majorArcSubdivisionWidth]
    positivity
  have hB : B ≤ L ^ (5 * D + 10) := by simpa [B, C0, L, x] using hbound
  have hpower :
      L ^ (5 * D + 10) * L ^ (D + k) * L ^ (4 * D) ≤ L ^ N := by
    rw [← pow_add, ← pow_add]
    apply pow_le_pow_right₀ hL.le
    dsimp [N, majorArcLogSubdivisionExponent]
    omega
  have hLPos : 0 < L := zero_lt_one.trans hL
  have hratio :
      (L ^ (5 * D + 10) * L ^ (D + k)) / L ^ N ≤
        1 / L ^ (4 * D) := by
    apply (div_le_div_iff₀ (pow_pos hLPos N) (pow_pos hLPos (4 * D))).2
    simpa using hpower
  calc
    (E + 1 + 2 * Real.pi * |(c : Real)| * Real.log 4 + Real.log 4) *
          majorArcSubdivisionWidth
            (majorArcLogSubdivisionCount X D (k + 1)) * (X : Real) *
          (2 * Real.log 4 * Real.log (X : Real)) ^ k =
        ((E + 1 + 2 * Real.pi * |(c : Real)| * Real.log 4 + Real.log 4) *
          (C0 * L) ^ k) *
          majorArcSubdivisionWidth
            (majorArcLogSubdivisionCount X D (k + 1)) * x := by
      dsimp [C0, L, x]
      ring
    _ ≤ (B * L ^ (D + k)) * (L ^ N)⁻¹ * x := by gcongr
    _ ≤ (L ^ (5 * D + 10) * L ^ (D + k)) * (L ^ N)⁻¹ * x := by
      gcongr
    _ = ((L ^ (5 * D + 10) * L ^ (D + k)) / L ^ N) * x := by
      rw [div_eq_mul_inv]
    _ ≤ (1 / L ^ (4 * D)) * x := by gcongr
    _ = (X : Real) / Real.log (X : Real) ^ (4 * D) := by
      dsimp [L, x]
      ring

private theorem majorArcM2LogScaleCoefficient_le_of_bounds
    {X D k R : Nat} {eta E : Real} {c : Int}
    (hX : 4 ≤ X) (hk : k ≤ R) (hE : 0 ≤ E)
    (hc : |(c : Real)| ≤ Real.log (X : Real) ^ D)
    (hfirst :
      Real.log 4 * (2 * Real.log 4) ^ R *
          Real.log (X : Real) ^ (R + 4 * D) ≤ (X : Real) ^ (eta / 12))
    (hsecond :
      Real.log 4 * (2 * Real.log 4) ^ R *
          Real.log (X : Real) ^ (R + 4 * D) ≤
        (X : Real) ^ (majorArcM2LogLogDelta X))
    (hblock :
      (E + 1 + 2 * Real.pi * Real.log 4 + Real.log 4) *
          (2 * Real.log 4) ^ R ≤
        Real.log (X : Real) ^ (5 * D + 10)) :
    majorArcM2LogScaleCoefficient X D k eta E c ≤
      3 * (X : Real) / Real.log (X : Real) ^ (4 * D) := by
  have hxPos : (0 : Real) < X := by positivity
  have hL : 1 ≤ Real.log (X : Real) := by
    have hXpos : (0 : Real) < X := by positivity
    exact ((Real.lt_log_iff_exp_lt hXpos).mpr <|
      Real.exp_one_lt_three.trans_le
        (by exact_mod_cast (show 3 ≤ X by omega))).le
  have hC0 : 1 ≤ 2 * Real.log 4 := by
    have : (1 : Real) < Real.log 4 :=
      (Real.lt_log_iff_exp_lt (by norm_num)).2
        (Real.exp_one_lt_three.trans_le (by norm_num))
    linarith
  have htermOne := majorArcM2RelaxationTerm_le
    hxPos hL hk hC0 hfirst
  have htermTwo := majorArcM2RelaxationTerm_le
    hxPos hL hk hC0 hsecond
  have htermTwo' :
      Real.log 4 * (X : Real) ^
          (1 - (Real.log (Real.log (X : Real)))⁻¹) *
          (2 * Real.log 4 * Real.log (X : Real)) ^ k ≤
        (X : Real) / Real.log (X : Real) ^ (4 * D) := by
    simpa [majorArcM2LogLogDelta] using htermTwo
  have htermBlock := majorArcM2BlockTerm_le hX hk hE hc hblock
  unfold majorArcM2LogScaleCoefficient majorArcM2RelaxationScale
    majorArcM2LogLogDelta
  calc
    (Real.log 4 *
          ((X : Real) ^ (1 - eta / 12) +
            (X : Real) ^ (1 - (Real.log (Real.log (X : Real)))⁻¹)) +
        (E + 1 + 2 * Real.pi * |(c : Real)| * Real.log 4 + Real.log 4) *
          majorArcSubdivisionWidth
            (majorArcLogSubdivisionCount X D (k + 1)) * (X : Real)) *
        (2 * Real.log 4 * Real.log (X : Real)) ^ k =
      Real.log 4 * (X : Real) ^ (1 - eta / 12) *
          (2 * Real.log 4 * Real.log (X : Real)) ^ k +
        Real.log 4 * (X : Real) ^
            (1 - (Real.log (Real.log (X : Real)))⁻¹) *
          (2 * Real.log 4 * Real.log (X : Real)) ^ k +
        (E + 1 + 2 * Real.pi * |(c : Real)| * Real.log 4 + Real.log 4) *
          majorArcSubdivisionWidth
            (majorArcLogSubdivisionCount X D (k + 1)) * (X : Real) *
          (2 * Real.log 4 * Real.log (X : Real)) ^ k := by ring
    _ ≤ (X : Real) / Real.log (X : Real) ^ (4 * D) +
        (X : Real) / Real.log (X : Real) ^ (4 * D) +
        (X : Real) / Real.log (X : Real) ^ (4 * D) :=
      add_le_add (add_le_add htermOne htermTwo') htermBlock
    _ = 3 * (X : Real) / Real.log (X : Real) ^ (4 * D) := by ring

/--
For fixed outer parameters, every remaining term is absorbed uniformly over bounded prefix
arity and the full signed offset range.
-/
theorem exists_majorArcM2LogScaleThreshold
    (D R : Nat) {eta E : Real} (heta : 0 < eta) (hE : 0 ≤ E) :
    ∃ X0 : Nat, ∀ X : Nat, X0 ≤ X →
      4 ≤ X ∧
      Real.log (X : Real) ^ D ≤ (X : Real) ∧
      Real.exp (Real.exp (12 / eta ^ 2)) ≤ (X : Real) ∧
      5 < (X : Real) ^ (eta / 4) ∧
      ∀ k : Nat, k ≤ R → ∀ c : Int,
        |(c : Real)| ≤ Real.log (X : Real) ^ D →
        majorArcM2LogScaleCoefficient X D k eta E c ≤
          3 * (X : Real) / Real.log (X : Real) ^ (4 * D) := by
  let A := Real.log 4 * (2 * Real.log 4) ^ R
  let B := (E + 1 + 2 * Real.pi * Real.log 4 + Real.log 4) *
    (2 * Real.log 4) ^ R
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hfirst := eventually_const_mul_log_pow_le_rpow
    A (R + 4 * D) hA (show 0 < eta / 12 by positivity)
  have hsecond := eventually_const_mul_log_pow_le_rpow_inv_log_log
    A (R + 4 * D)
  have hlogPower : ∀ᶠ x : Real in atTop,
      Real.log x ^ D ≤ x := by
    simpa only [one_mul, Real.rpow_one] using
      (eventually_const_mul_log_pow_le_rpow
        1 D zero_le_one (show (0 : Real) < 1 by norm_num))
  have hblockLog :=
    Real.tendsto_log_atTop.eventually_ge_atTop (max B 1)
  have hblock : ∀ᶠ x : Real in atTop,
      B ≤ Real.log x ^ (5 * D + 10) := by
    filter_upwards [hblockLog] with x hx
    have hBone : B ≤ Real.log x :=
      (le_max_left B 1).trans hx
    have hlogOne : 1 ≤ Real.log x :=
      (le_max_right B 1).trans hx
    exact hBone.trans (le_self_pow₀ hlogOne (by omega))
  have hlarge :=
    (tendsto_rpow_atTop (show 0 < eta / 4 by positivity)).eventually_gt_atTop 5
  have hall : ∀ᶠ x : Real in atTop,
      (4 : Real) ≤ x ∧
      Real.log x ^ D ≤ x ∧
      Real.exp (Real.exp (12 / eta ^ 2)) ≤ x ∧
      5 < x ^ (eta / 4) ∧
      A * Real.log x ^ (R + 4 * D) ≤ x ^ (eta / 12) ∧
      A * Real.log x ^ (R + 4 * D) ≤
        x ^ (Real.log (Real.log x))⁻¹ ∧
      B ≤ Real.log x ^ (5 * D + 10) := by
    filter_upwards [eventually_ge_atTop (4 : Real), hlogPower,
      eventually_ge_atTop (Real.exp (Real.exp (12 / eta ^ 2))),
      hlarge, hfirst, hsecond, hblock] with x hx4 hxLog hxExp hxLarge
        hxFirst hxSecond hxBlock
    exact ⟨hx4, hxLog, hxExp, hxLarge, hxFirst, hxSecond, hxBlock⟩
  rcases eventually_atTop.mp hall with ⟨M, hM⟩
  let X0 := Nat.ceil (max M 4)
  refine ⟨X0, ?_⟩
  intro X hX
  have hMX0 : M ≤ (X0 : Real) :=
    (le_max_left M 4).trans (Nat.le_ceil (max M 4))
  have hX0X : (X0 : Real) ≤ X := by exact_mod_cast hX
  rcases hM (X : Real) (hMX0.trans hX0X) with
    ⟨hX4, hXLog, hXExp, hXLarge, hXFirst, hXSecond, hXBlock⟩
  refine ⟨by exact_mod_cast hX4, hXLog, hXExp, hXLarge, ?_⟩
  intro k hk c hc
  apply majorArcM2LogScaleCoefficient_le_of_bounds
    (by exact_mod_cast hX4) hk hE hc
  · simpa [A] using hXFirst
  · simpa [A, majorArcM2LogLogDelta] using hXSecond
  · simpa [B] using hXBlock

end PrimesRestrictedDigits
