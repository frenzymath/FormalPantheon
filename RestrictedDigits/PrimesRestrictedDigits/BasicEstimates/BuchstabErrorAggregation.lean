import PrimesRestrictedDigits.BasicEstimates.ReciprocalPrimeInterval

/-!
# Error aggregation on a Buchstab induction slab

These are the two elementary error estimates in the induction step of
`MONTGOMERY-VAUGHAN-MNT-I`, Theorem 7.11, p. 218, following Eq. (7.45).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The log-square remainder scales aggregate over one natural Buchstab slab
with an absolute coefficient. -/
theorem sum_prime_buchstab_remainder_scale_le
    {m : Nat} {x u : Real}
    (hx : 1 < x) (hm : 2 <= m)
    (hmu : (m : Real) <= u) (hu : u <= (m : Real) + 1)
    (hlower : 2 <= x ^ (1 / u)) :
    (∑ p ∈
      (naturalLeftClosedRightOpenInterval (x ^ (1 / u))
        (x ^ (1 / (m : Real)))).filter Nat.Prime,
      (x / (p : Real)) / Real.log (x / (p : Real)) ^ 2) <=
      4 * Real.log 4 * ((3 / 2 : Real) + (Real.log 2)⁻¹) *
        (x / Real.log x ^ 2) := by
  let a : Real := x ^ (1 / u)
  let b : Real := x ^ (1 / (m : Real))
  let D : Real := Real.log 4 * ((3 / 2 : Real) + (Real.log 2)⁻¹)
  let c : Real := 4 * x / Real.log x ^ 2
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hmReal : (2 : Real) <= (m : Real) := by exact_mod_cast hm
  have hrec :
      (∑ p ∈ (naturalLeftClosedRightOpenInterval a b).filter Nat.Prime,
        (p : Real)⁻¹) <= D := by
    simpa [a, b, D] using
      sum_prime_inv_buchstabSlab_le x (m : Real) u hx0 hmReal hmu hu hlower
  have hc0 : 0 <= c := by dsimp [c]; positivity
  have hpoint : ∀ p ∈
      (naturalLeftClosedRightOpenInterval a b).filter Nat.Prime,
      (x / (p : Real)) / Real.log (x / (p : Real)) ^ 2 <=
        c * (p : Real)⁻¹ := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpBounds := mem_naturalLeftClosedRightOpenInterval.mp hpData.1
    have hp0 : 0 < (p : Real) := by exact_mod_cast hpData.2.pos
    have hpb : (p : Real) <= b := hpBounds.2.le
    have hlogp_le : Real.log (p : Real) <= Real.log x / 2 := by
      have hlogpb : Real.log (p : Real) <= Real.log b :=
        Real.log_le_log hp0 hpb
      have hloginv : 1 / (m : Real) <= (1 / 2 : Real) :=
        one_div_le_one_div_of_le (by norm_num) hmReal
      calc
        Real.log (p : Real) <= Real.log b := hlogpb
        _ = (1 / (m : Real)) * Real.log x := by
          dsimp [b]
          exact Real.log_rpow hx0 (1 / (m : Real))
        _ <= (1 / 2 : Real) * Real.log x :=
          mul_le_mul_of_nonneg_right hloginv hlogx.le
        _ = Real.log x / 2 := by ring
    have hlogdiv :
        Real.log (x / (p : Real)) = Real.log x - Real.log (p : Real) :=
      Real.log_div hx0.ne' hp0.ne'
    have hhalf : Real.log x / 2 <= Real.log (x / (p : Real)) := by
      rw [hlogdiv]
      linarith
    have hlogdiv0 : 0 < Real.log (x / (p : Real)) :=
      (by positivity : 0 < Real.log x / 2).trans_le hhalf
    have hsqHalf :
        (Real.log x / 2) ^ 2 <= Real.log (x / (p : Real)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hhalf 2
    have hsq :
        Real.log x ^ 2 <= 4 * Real.log (x / (p : Real)) ^ 2 := by
      nlinarith
    have hinvSq :
        1 / Real.log (x / (p : Real)) ^ 2 <= 4 / Real.log x ^ 2 := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hlogdiv0) (sq_pos_of_pos hlogx)]
      simpa using hsq
    calc
      (x / (p : Real)) / Real.log (x / (p : Real)) ^ 2 =
          (x / (p : Real)) *
            (1 / Real.log (x / (p : Real)) ^ 2) := by ring
      _ <= (x / (p : Real)) * (4 / Real.log x ^ 2) :=
        mul_le_mul_of_nonneg_left hinvSq (by positivity)
      _ = c * (p : Real)⁻¹ := by
        dsimp [c]
        field_simp [hp0.ne', hlogx.ne']

  change (∑ p ∈ (naturalLeftClosedRightOpenInterval a b).filter Nat.Prime,
      (x / (p : Real)) / Real.log (x / (p : Real)) ^ 2) <= _
  calc
    (∑ p ∈ (naturalLeftClosedRightOpenInterval a b).filter Nat.Prime,
        (x / (p : Real)) / Real.log (x / (p : Real)) ^ 2) <=
        ∑ p ∈ (naturalLeftClosedRightOpenInterval a b).filter Nat.Prime,
          c * (p : Real)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      exact hpoint p hp
    _ = c * (∑ p ∈
        (naturalLeftClosedRightOpenInterval a b).filter Nat.Prime,
          (p : Real)⁻¹) := by
      rw [Finset.mul_sum]
    _ <= c * D := mul_le_mul_of_nonneg_left hrec hc0
    _ = 4 * Real.log 4 * ((3 / 2 : Real) + (Real.log 2)⁻¹) *
        (x / Real.log x ^ 2) := by
      dsimp [c, D]
      ring

/-- The endpoint and secondary prime-weight discrepancies on one natural slab
have a uniform log-square bound. -/
theorem abs_buchstab_secondary_discrepancy_le
    {m : Nat} {x u : Real}
    (hx : 1 < x) (hm : 2 <= m)
    (hmu : (m : Real) <= u) (hu : u <= (m : Real) + 1)
    (hlower : 2 <= x ^ (1 / u)) :
    |x ^ (1 / u) / Real.log (x ^ (1 / u)) -
        x ^ (1 / (m : Real)) / Real.log (x ^ (1 / (m : Real))) -
        ∑ p ∈
          (naturalLeftClosedRightOpenInterval (x ^ (1 / u))
            (x ^ (1 / (m : Real)))).filter Nat.Prime,
          (p : Real) / Real.log p| <=
      (4 + Real.log 4) * ((m : Real) + 1) ^ 2 *
        (x / Real.log x ^ 2) := by
  let a : Real := x ^ (1 / u)
  let b : Real := x ^ (1 / (m : Real))
  let M : Real := (m : Real) + 1
  let s : Finset Nat :=
    (naturalLeftClosedRightOpenInterval a b).filter Nat.Prime
  let scale : Real := x / Real.log x ^ 2
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hmReal : (2 : Real) <= (m : Real) := by exact_mod_cast hm
  have hm0 : 0 < (m : Real) := by linarith
  have hu0 : 0 < u := hm0.trans_le hmu
  have huM : u <= M := by simpa [M] using hu
  have hmM : (m : Real) <= M := by dsimp [M]; linarith
  have hscale0 : 0 <= scale := by dsimp [scale]; positivity
  have hab : a <= b := by
    dsimp [a, b]
    apply Real.rpow_le_rpow_of_exponent_le hx.le
    exact one_div_le_one_div_of_le hm0 hmu
  have ha2 : 2 <= a := by simpa [a] using hlower
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := ha0.trans_le hab
  have hloga : 0 < Real.log a := Real.log_pos (by linarith)
  have hlogb : 0 < Real.log b := Real.log_pos (by linarith [ha2, hab])
  have hlogaEq : Real.log a = (1 / u) * Real.log x := by
    dsimp [a]
    exact Real.log_rpow hx0 (1 / u)
  have hpowerSqrt : ∀ {v : Real}, 2 <= v ->
      x ^ (1 / v) <= Real.sqrt x := by
    intro v hv
    rw [Real.sqrt_eq_rpow]
    apply Real.rpow_le_rpow_of_exponent_le hx.le
    exact one_div_le_one_div_of_le (by norm_num) hv
  have hbSqrt : b <= Real.sqrt x := by
    simpa [b] using hpowerSqrt hmReal
  have hbSq : b ^ 2 <= x := by
    calc
      b ^ 2 <= (Real.sqrt x) ^ 2 :=
        pow_le_pow_left₀ hb0.le hbSqrt 2
      _ = x := Real.sq_sqrt hx0.le
  have hlogSqrt : Real.log x <= 2 * Real.sqrt x := by
    have h := Real.log_le_rpow_div hx0.le
      (by norm_num : (0 : Real) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    nlinarith
  have hendpoint : ∀ {v : Real}, 2 <= v -> v <= M ->
      x ^ (1 / v) / Real.log (x ^ (1 / v)) <=
        2 * M * scale := by
    intro v hv hvM
    have hv0 : 0 < v := by linarith
    let t : Real := x ^ (1 / v)
    have ht0 : 0 < t := by dsimp [t]; positivity
    have htSqrt : t <= Real.sqrt x := by
      dsimp [t]
      exact hpowerSqrt hv
    have hlogt : Real.log t = (1 / v) * Real.log x := by
      dsimp [t]
      exact Real.log_rpow hx0 (1 / v)
    have hnum : v * t * Real.log x <= 2 * M * x := by
      calc
        v * t * Real.log x <= M * Real.sqrt x * (2 * Real.sqrt x) := by
          gcongr
        _ = 2 * M * (Real.sqrt x) ^ 2 := by ring
        _ = 2 * M * x := by rw [Real.sq_sqrt hx0.le]
    have heq : t / Real.log t =
        (v * t * Real.log x) / Real.log x ^ 2 := by
      rw [hlogt]
      field_simp [hv0.ne', hlogx.ne']

    change t / Real.log t <= _
    rw [heq]
    calc
      (v * t * Real.log x) / Real.log x ^ 2 <=
          (2 * M * x) / Real.log x ^ 2 :=
        div_le_div_of_nonneg_right hnum (sq_nonneg _)
      _ = 2 * M * scale := by dsimp [scale]; ring
  have hEndpointA : a / Real.log a <= 2 * M * scale := by
    simpa [a] using hendpoint (v := u) (hmReal.trans hmu) huM
  have hEndpointB : b / Real.log b <= 2 * M * scale := by
    simpa [b] using hendpoint (v := (m : Real)) hmReal hmM
  have hsubset : s ⊆ Nat.primesLE (Nat.floor b) := by
    intro p hp
    have hpData := Finset.mem_filter.mp (by simpa [s] using hp)
    have hpBounds := mem_naturalLeftClosedRightOpenInterval.mp hpData.1
    apply Nat.mem_primesLE.mpr
    exact ⟨(Nat.le_floor_iff hb0.le).mpr hpBounds.2.le, hpData.2⟩
  have hsumLog : (∑ p ∈ s, Real.log (p : Real)) <= Real.log 4 * b := by
    calc
      (∑ p ∈ s, Real.log (p : Real)) <=
          ∑ p ∈ Nat.primesLE (Nat.floor b), Real.log (p : Real) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro p hp hps
        exact Real.log_natCast_nonneg p
      _ = Chebyshev.theta b := (Chebyshev.theta_eq_sum_primesLE b).symm
      _ <= Real.log 4 * b := Chebyshev.theta_le_log4_mul_x hb0.le
  have hprimePoint : ∀ p ∈ s,
      (p : Real) / Real.log p <= b * Real.log p / Real.log a ^ 2 := by
    intro p hp
    have hpData := Finset.mem_filter.mp (by simpa [s] using hp)
    have hpBounds := mem_naturalLeftClosedRightOpenInterval.mp hpData.1
    have hp0 : 0 < (p : Real) := by exact_mod_cast hpData.2.pos
    have hlogp : 0 < Real.log (p : Real) :=
      Real.log_pos (by exact_mod_cast hpData.2.one_lt)
    have hlogap : Real.log a <= Real.log (p : Real) :=
      Real.log_le_log ha0 hpBounds.1
    rw [div_le_div_iff₀ hlogp (sq_pos_of_pos hloga)]
    calc
      (p : Real) * Real.log a ^ 2 <= b * Real.log a ^ 2 :=
        mul_le_mul_of_nonneg_right hpBounds.2.le (sq_nonneg _)
      _ <= b * Real.log (p : Real) ^ 2 :=
        mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ hloga.le hlogp.le).mpr hlogap) hb0.le
      _ = b * Real.log (p : Real) * Real.log (p : Real) := by ring
  have hprimeSum :
      (∑ p ∈ s, (p : Real) / Real.log p) <=
        Real.log 4 * M ^ 2 * scale := by
    have hcoef0 : 0 <= b / Real.log a ^ 2 := by positivity
    have hraw :
        (∑ p ∈ s, (p : Real) / Real.log p) <=
          Real.log 4 * b ^ 2 / Real.log a ^ 2 := by
      calc
        (∑ p ∈ s, (p : Real) / Real.log p) <=
            ∑ p ∈ s, b * Real.log p / Real.log a ^ 2 := by
          apply Finset.sum_le_sum
          intro p hp
          exact hprimePoint p hp
        _ = (b / Real.log a ^ 2) *
            (∑ p ∈ s, Real.log (p : Real)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          ring
        _ <= (b / Real.log a ^ 2) * (Real.log 4 * b) :=
          mul_le_mul_of_nonneg_left hsumLog hcoef0
        _ = Real.log 4 * b ^ 2 / Real.log a ^ 2 := by ring
    have huSq : u ^ 2 <= M ^ 2 :=
      pow_le_pow_left₀ hu0.le huM 2
    have hnum : u ^ 2 * b ^ 2 <= M ^ 2 * x :=
      mul_le_mul huSq hbSq (sq_nonneg b) (sq_nonneg M)
    have hscaleB : b ^ 2 / Real.log a ^ 2 <= M ^ 2 * scale := by
      have heq : b ^ 2 / Real.log a ^ 2 =
          (u ^ 2 * b ^ 2) / Real.log x ^ 2 := by
        rw [hlogaEq]
        field_simp [hu0.ne', hlogx.ne']

      rw [heq]
      calc
        (u ^ 2 * b ^ 2) / Real.log x ^ 2 <=
            (M ^ 2 * x) / Real.log x ^ 2 :=
          div_le_div_of_nonneg_right hnum (sq_nonneg _)
        _ = M ^ 2 * scale := by dsimp [scale]; ring
    have hlog4 : 0 <= Real.log 4 := Real.log_nonneg (by norm_num)
    apply hraw.trans
    calc
      Real.log 4 * b ^ 2 / Real.log a ^ 2 =
          Real.log 4 * (b ^ 2 / Real.log a ^ 2) := by ring
      _ <= Real.log 4 * (M ^ 2 * scale) :=
        mul_le_mul_of_nonneg_left hscaleB hlog4
      _ = Real.log 4 * M ^ 2 * scale := by ring
  have hsum0 : 0 <= ∑ p ∈ s, (p : Real) / Real.log p := by
    apply Finset.sum_nonneg
    intro p hp
    have hpData := Finset.mem_filter.mp (by simpa [s] using hp)
    have hp0 : 0 < Real.log (p : Real) :=
      Real.log_pos (by exact_mod_cast hpData.2.one_lt)
    positivity
  have habs :
      |a / Real.log a - b / Real.log b -
          ∑ p ∈ s, (p : Real) / Real.log p| <=
        a / Real.log a + b / Real.log b +
          ∑ p ∈ s, (p : Real) / Real.log p := by
    calc
      |a / Real.log a - b / Real.log b -
          ∑ p ∈ s, (p : Real) / Real.log p| <=
          |a / Real.log a - b / Real.log b| +
            |∑ p ∈ s, (p : Real) / Real.log p| := abs_sub _ _
      _ <= (|a / Real.log a| + |b / Real.log b|) +
          |∑ p ∈ s, (p : Real) / Real.log p| := by
        exact add_le_add (abs_sub _ _) le_rfl
      _ = a / Real.log a + b / Real.log b +
          ∑ p ∈ s, (p : Real) / Real.log p := by
        rw [abs_of_nonneg (by positivity : 0 <= a / Real.log a),
          abs_of_nonneg (by positivity : 0 <= b / Real.log b),
          abs_of_nonneg hsum0]
  have hEndpointA' : a / Real.log a <= 2 * M ^ 2 * scale :=
    hEndpointA.trans (mul_le_mul_of_nonneg_right
      (by nlinarith [hu0, huM] : 2 * M <= 2 * M ^ 2) hscale0)
  have hEndpointB' : b / Real.log b <= 2 * M ^ 2 * scale :=
    hEndpointB.trans (mul_le_mul_of_nonneg_right
      (by nlinarith [hu0, huM] : 2 * M <= 2 * M ^ 2) hscale0)
  change |a / Real.log a - b / Real.log b -
      ∑ p ∈ s, (p : Real) / Real.log p| <= _
  apply habs.trans
  calc
    a / Real.log a + b / Real.log b +
        ∑ p ∈ s, (p : Real) / Real.log p <=
      2 * M ^ 2 * scale + 2 * M ^ 2 * scale +
        Real.log 4 * M ^ 2 * scale :=
      add_le_add (add_le_add hEndpointA' hEndpointB') hprimeSum
    _ = (4 + Real.log 4) * M ^ 2 * scale := by ring
    _ = (4 + Real.log 4) * ((m : Real) + 1) ^ 2 *
        (x / Real.log x ^ 2) := by rfl

end PrimesRestrictedDigits
