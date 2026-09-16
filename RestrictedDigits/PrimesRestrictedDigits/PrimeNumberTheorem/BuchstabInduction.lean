import PrimesRestrictedDigits.BasicEstimates.BuchstabErrorAggregation
import PrimesRestrictedDigits.BasicEstimates.BuchstabRecurrence
import PrimesRestrictedDigits.PrimeNumberTheorem.BuchstabBase
import PrimesRestrictedDigits.PrimeNumberTheorem.BuchstabPrimeSumGlobal

/-!
# The quantitative Buchstab induction

This completes the induction in Montgomery--Vaughan, Chapter 7, proof of
Theorem 7.11 (pp. 217--218). The natural-index invariant is first propagated
across every unit slab and is then wrapped over an arbitrary fixed real upper
bound.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

private theorem buchstabPhi_error_succ
    {m : Nat} (hm : 2 <= m) {C B : Real} (hC : 0 < C) (hB : 0 < B)
    (ih : forall x y u : Real, 0 < x -> 2 <= y -> 1 <= u ->
      u <= (m : Real) -> u = Real.log x / Real.log y ->
      |(buchstabPhi x y : Real) -
        (buchstabFunction u * x / Real.log y - y / Real.log y)| <=
        C * (x / Real.log x ^ 2))
    (hweight : forall x u : Real, 1 < x -> (m : Real) <= u ->
      u <= (m : Real) + 1 -> 2 <= x ^ (1 / u) ->
      |(∑ p ∈ (naturalLeftClosedRightOpenInterval (x ^ (1 / u))
          (x ^ (1 / (m : Real)))).filter Nat.Prime,
          buchstabPrimeWeight x p) -
        x / Real.log x * (u * buchstabFunction u -
          (m : Real) * buchstabFunction (m : Real))| <=
        B * ((m : Real) + 1) ^ 2 * (x / Real.log x ^ 2)) :
    forall x y u : Real, 0 < x -> 2 <= y -> 1 <= u ->
      u <= ((m + 1 : Nat) : Real) -> u = Real.log x / Real.log y ->
      |(buchstabPhi x y : Real) -
        (buchstabFunction u * x / Real.log y - y / Real.log y)| <=
      (C * (1 + 4 * Real.log 4 *
          ((3 / 2 : Real) + (Real.log 2)⁻¹)) +
        (B + 4 + Real.log 4) * ((m : Real) + 1) ^ 2) *
        (x / Real.log x ^ 2) := by
  intro x y u hx hy hu huSucc heq
  let K : Real := 4 * Real.log 4 *
    ((3 / 2 : Real) + (Real.log 2)⁻¹)
  let Cnext : Real := C * (1 + K) +
    (B + 4 + Real.log 4) * ((m : Real) + 1) ^ 2
  have hK : 0 <= K := by dsimp [K]; positivity
  have hCnext : C <= Cnext := by
    have hfirst : 0 <= C * K := mul_nonneg hC.le hK
    have hsecond : 0 <=
        (B + 4 + Real.log 4) * ((m : Real) + 1) ^ 2 := by positivity
    dsimp [Cnext]
    nlinarith
  have hscale : 0 <= x / Real.log x ^ 2 := by positivity
  by_cases hum : u <= (m : Real)
  · apply (ih x y u hx hy hu hum heq).trans
    change C * (x / Real.log x ^ 2) <= Cnext * (x / Real.log x ^ 2)
    exact mul_le_mul_of_nonneg_right hCnext hscale
  have hmu : (m : Real) <= u := le_of_lt (lt_of_not_ge hum)
  have huSlab : u <= (m : Real) + 1 := by
    norm_num at huSucc ⊢
    exact huSucc
  have hypos : 0 < y := by linarith
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hu0 : 0 < u := by linarith
  have hlogxEq : Real.log x = u * Real.log y := by
    rw [heq]
    field_simp
  have hlogx : 0 < Real.log x := by rw [hlogxEq]; positivity
  have hx1 : 1 < x := (Real.log_pos_iff hx.le).mp hlogx
  have hlogPower : Real.log (x ^ (1 / u)) = Real.log y := by
    rw [Real.log_rpow hx, hlogxEq]
    field_simp
  have hyPower : y = x ^ (1 / u) := by
    calc
      y = Real.exp (Real.log y) := (Real.exp_log hypos).symm
      _ = Real.exp (Real.log (x ^ (1 / u))) := by rw [hlogPower]
      _ = x ^ (1 / u) := Real.exp_log (Real.rpow_pos_of_pos hx _)
  let a : Real := x ^ (1 / u)
  let b : Real := x ^ (1 / (m : Real))
  let primes : Finset Nat :=
    (naturalLeftClosedRightOpenInterval a b).filter Nat.Prime
  have hm0 : 0 < (m : Real) := by positivity
  have hab : a <= b := by
    dsimp [a, b]
    apply Real.rpow_le_rpow_of_exponent_le hx1.le
    exact one_div_le_one_div_of_le hm0 hmu
  have ha2 : 2 <= a := by simpa [a, ← hyPower] using hy
  have hb2 : 2 <= b := ha2.trans hab
  have hloga : Real.log a = (1 / u) * Real.log x := by
    dsimp [a]
    exact Real.log_rpow hx (1 / u)
  have hlogb : Real.log b = (1 / (m : Real)) * Real.log x := by
    dsimp [b]
    exact Real.log_rpow hx (1 / (m : Real))
  have hmParam : (m : Real) = Real.log x / Real.log b := by
    rw [hlogb]
    field_simp
  have hmOne : (1 : Real) <= (m : Real) := by
    exact_mod_cast (show 1 <= m by omega)
  have houter := ih x b (m : Real) hx hb2 hmOne le_rfl hmParam
  have hinner : ∀ p ∈ primes,
      |(buchstabPhi (x / (p : Real)) (p : Real) : Real) -
          (buchstabPrimeWeight x p - (p : Real) / Real.log p)| <=
        C * ((x / (p : Real)) /
          Real.log (x / (p : Real)) ^ 2) := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpBounds := mem_naturalLeftClosedRightOpenInterval.mp hpData.1
    have hpPrime : p.Prime := hpData.2
    have hpPos : 0 < (p : Real) := by exact_mod_cast hpPrime.pos
    have hp0 : (p : Real) ≠ 0 := hpPos.ne'
    have hlogp : 0 < Real.log (p : Real) :=
      Real.log_pos (by exact_mod_cast hpPrime.one_lt)
    have hpIcc : (p : Real) ∈ Set.Icc a b :=
      ⟨hpBounds.1, hpBounds.2.le⟩
    have hargRange := buchstabArgument_mem_Icc_powerInterval
      hx1 (by omega : 0 < m) hmu hpIcc
    have hargOne : 1 <= buchstabArgument x (p : Real) := by
      have hmReal : (2 : Real) <= (m : Real) := by exact_mod_cast hm
      linarith [hargRange.1]
    have hargM : buchstabArgument x (p : Real) <= (m : Real) := by
      linarith [hargRange.2, huSlab]
    have hargEq : buchstabArgument x (p : Real) =
        Real.log (x / (p : Real)) / Real.log (p : Real) := by
      rw [Real.log_div hx.ne' hp0]
      unfold buchstabArgument
      rw [sub_div, div_self hlogp.ne']
    have hxp : 0 < x / (p : Real) := div_pos hx hpPos
    have hi := ih (x / (p : Real)) (p : Real)
      (buchstabArgument x (p : Real)) hxp (by exact_mod_cast hpPrime.two_le)
      hargOne hargM hargEq
    have hmain :
        buchstabFunction (buchstabArgument x (p : Real)) *
              (x / (p : Real)) / Real.log (p : Real) =
            buchstabPrimeWeight x p := by
      unfold buchstabPrimeWeight
      ring
    rw [hmain] at hi
    exact hi
  have hinnerSum :
      |(∑ p ∈ primes,
          (buchstabPhi (x / (p : Real)) (p : Real) : Real)) -
          ∑ p ∈ primes, (buchstabPrimeWeight x p -
            (p : Real) / Real.log p)| <=
        C * K * (x / Real.log x ^ 2) := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ p ∈ primes,
          ((buchstabPhi (x / (p : Real)) (p : Real) : Real) -
            (buchstabPrimeWeight x p - (p : Real) / Real.log p))| <=
          ∑ p ∈ primes,
            |(buchstabPhi (x / (p : Real)) (p : Real) : Real) -
              (buchstabPrimeWeight x p - (p : Real) / Real.log p)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= ∑ p ∈ primes, C * ((x / (p : Real)) /
          Real.log (x / (p : Real)) ^ 2) := by
        apply Finset.sum_le_sum
        intro p hp
        exact hinner p hp
      _ = C * (∑ p ∈ primes, (x / (p : Real)) /
          Real.log (x / (p : Real)) ^ 2) := by
        rw [Finset.mul_sum]
      _ <= C * (K * (x / Real.log x ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hC.le
        simpa [K, primes, a, b] using
          sum_prime_buchstab_remainder_scale_le hx1 hm hmu huSlab ha2
      _ = C * K * (x / Real.log x ^ 2) := by ring
  have hweighted :
      |(∑ p ∈ primes, buchstabPrimeWeight x p) -
        x / Real.log x * (u * buchstabFunction u -
          (m : Real) * buchstabFunction (m : Real))| <=
        B * ((m : Real) + 1) ^ 2 *
          (x / Real.log x ^ 2) := by
    simpa [primes, a, b] using hweight x u hx1 hmu huSlab ha2
  have hsecondary :
      |a / Real.log a - b / Real.log b -
          ∑ p ∈ primes, (p : Real) / Real.log p| <=
        (4 + Real.log 4) * ((m : Real) + 1) ^ 2 *
          (x / Real.log x ^ 2) := by
    simpa [primes, a, b] using
      abs_buchstab_secondary_discrepancy_le hx1 hm hmu huSlab ha2
  have houterFirst :
      buchstabFunction (m : Real) * x / Real.log b =
        x / Real.log x * ((m : Real) * buchstabFunction (m : Real)) := by
    rw [hlogb]
    field_simp
  have htargetFirst :
      buchstabFunction u * x / Real.log a =
        x / Real.log x * (u * buchstabFunction u) := by
    rw [hloga]
    field_simp
  let outer : Real :=
    buchstabFunction (m : Real) * x / Real.log b - b / Real.log b
  let primeApprox : Real :=
    ∑ p ∈ primes, (buchstabPrimeWeight x p - (p : Real) / Real.log p)
  let weightedMain : Real := x / Real.log x *
    (u * buchstabFunction u - (m : Real) * buchstabFunction (m : Real))
  let target : Real :=
    buchstabFunction u * x / Real.log a - a / Real.log a
  have hrecNat := buchstabPhi_threshold_recurrence (x := x) hab
  have hrec : (buchstabPhi x a : Real) =
      (buchstabPhi x b : Real) +
        ∑ p ∈ primes,
          (buchstabPhi (x / (p : Real)) (p : Real) : Real) := by
    exact_mod_cast hrecNat
  have hlast : outer + weightedMain -
        (∑ p ∈ primes, (p : Real) / Real.log p) - target =
      a / Real.log a - b / Real.log b -
        ∑ p ∈ primes, (p : Real) / Real.log p := by
    dsimp [outer, weightedMain, target]
    rw [houterFirst, htargetFirst]
    ring
  have hprimeApprox : primeApprox =
      (∑ p ∈ primes, buchstabPrimeWeight x p) -
        ∑ p ∈ primes, (p : Real) / Real.log p := by
    dsimp [primeApprox]
    exact Finset.sum_sub_distrib _ _
  rw [hyPower, hrec]
  change |((buchstabPhi x b : Real) +
      ∑ p ∈ primes,
        (buchstabPhi (x / (p : Real)) (p : Real) : Real)) - target| <=
    Cnext * (x / Real.log x ^ 2)
  let actual : Real := (buchstabPhi x b : Real) +
    ∑ p ∈ primes, (buchstabPhi (x / (p : Real)) (p : Real) : Real)
  let z1 : Real := outer +
    ∑ p ∈ primes, (buchstabPhi (x / (p : Real)) (p : Real) : Real)
  let z2 : Real := outer + primeApprox
  let z3 : Real := outer + weightedMain -
    ∑ p ∈ primes, (p : Real) / Real.log p
  have hactualZ1 : actual - z1 = (buchstabPhi x b : Real) - outer := by
    dsimp [actual, z1]
    ring
  have hz1Z2 : z1 - z2 =
      (∑ p ∈ primes,
        (buchstabPhi (x / (p : Real)) (p : Real) : Real)) -
        primeApprox := by
    dsimp [z1, z2]
    ring
  have hz2Z3 : z2 - z3 =
      (∑ p ∈ primes, buchstabPrimeWeight x p) - weightedMain := by
    dsimp [z2, z3]
    rw [hprimeApprox]
    ring
  have hz3Target : z3 - target =
      a / Real.log a - b / Real.log b -
        ∑ p ∈ primes, (p : Real) / Real.log p := by
    dsimp [z3]
    exact hlast
  have htriangle : |actual - target| <=
      |(buchstabPhi x b : Real) - outer| +
        |(∑ p ∈ primes,
          (buchstabPhi (x / (p : Real)) (p : Real) : Real)) -
          primeApprox| +
        |(∑ p ∈ primes, buchstabPrimeWeight x p) - weightedMain| +
        |a / Real.log a - b / Real.log b -
          ∑ p ∈ primes, (p : Real) / Real.log p| := by
    calc
      |actual - target| <= |actual - z1| + |z1 - target| :=
        abs_sub_le actual z1 target
      _ <= |actual - z1| + (|z1 - z2| + |z2 - target|) := by
        gcongr
        exact abs_sub_le z1 z2 target
      _ <= |actual - z1| +
          (|z1 - z2| + (|z2 - z3| + |z3 - target|)) := by
        gcongr
        exact abs_sub_le z2 z3 target
      _ = _ := by rw [hactualZ1, hz1Z2, hz2Z3, hz3Target]; ring
  change |actual - target| <= Cnext * (x / Real.log x ^ 2)
  calc
    |actual - target| <=
        |(buchstabPhi x b : Real) - outer| +
          |(∑ p ∈ primes,
            (buchstabPhi (x / (p : Real)) (p : Real) : Real)) -
            primeApprox| +
          |(∑ p ∈ primes, buchstabPrimeWeight x p) - weightedMain| +
          |a / Real.log a - b / Real.log b -
            ∑ p ∈ primes, (p : Real) / Real.log p| := htriangle
    _ <= C * (x / Real.log x ^ 2) +
          C * K * (x / Real.log x ^ 2) +
          B * ((m : Real) + 1) ^ 2 * (x / Real.log x ^ 2) +
          (4 + Real.log 4) * ((m : Real) + 1) ^ 2 *
            (x / Real.log x ^ 2) := by
      exact add_le_add (add_le_add (add_le_add
        (by simpa [outer] using houter)
        (by simpa [primeApprox] using hinnerSum))
        (by simpa [weightedMain] using hweighted)) hsecondary
    _ = Cnext * (x / Real.log x ^ 2) := by
      dsimp [Cnext]
      ring

/-- The Buchstab estimate has a positive uniform coefficient through every
fixed natural upper bound for its logarithmic parameter. -/
theorem exists_buchstabPhi_error_nat :
    forall N : Nat, 2 <= N ->
      exists C : Real, 0 < C ∧
        forall x y u : Real, 0 < x -> 2 <= y -> 1 <= u ->
          u <= (N : Real) -> u = Real.log x / Real.log y ->
          |(buchstabPhi x y : Real) -
            (buchstabFunction u * x / Real.log y - y / Real.log y)| <=
            C * (x / Real.log x ^ 2) := by
  obtain ⟨B, hB, hweight⟩ := exists_buchstabPrimeWeight_error_bound
  obtain ⟨Cbase, hCbase, hbase⟩ := exists_buchstabPhi_base_error
  let P : Nat -> Prop := fun N =>
    exists C : Real, 0 < C ∧
      forall x y u : Real, 0 < x -> 2 <= y -> 1 <= u ->
        u <= (N : Real) -> u = Real.log x / Real.log y ->
        |(buchstabPhi x y : Real) -
          (buchstabFunction u * x / Real.log y - y / Real.log y)| <=
          C * (x / Real.log x ^ 2)
  have hbaseP : P 2 := by
    refine ⟨Cbase, hCbase, ?_⟩
    intro x y u hx hy hu hu2 heq
    have hypos : 0 < y := by linarith
    have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
    have hlogxEq : Real.log x = u * Real.log y := by
      rw [heq]
      field_simp
    have hlogx : 0 < Real.log x := by rw [hlogxEq]; positivity
    have hlogyx : Real.log y <= Real.log x := by
      rw [hlogxEq]
      nlinarith
    have hyx : y <= x := by
      calc
        y = Real.exp (Real.log y) := (Real.exp_log hypos).symm
        _ <= Real.exp (Real.log x) := Real.exp_le_exp.mpr hlogyx
        _ = x := Real.exp_log hx
    have hrootPos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
    have huTwo : u <= (2 : Real) := by
      norm_num at hu2 ⊢
      exact hu2
    have hlogRoot : Real.log (Real.sqrt x) <= Real.log y := by
      rw [Real.log_sqrt hx.le, hlogxEq]
      nlinarith [mul_nonneg (sub_nonneg.mpr huTwo) hlogy.le]
    have hroot : Real.sqrt x <= y := by
      calc
        Real.sqrt x = Real.exp (Real.log (Real.sqrt x)) :=
          (Real.exp_log hrootPos).symm
        _ <= Real.exp (Real.log y) := Real.exp_le_exp.mpr hlogRoot
        _ = y := Real.exp_log hypos
    have hmain :
        buchstabFunction u * x / Real.log y = x / Real.log x := by
      rw [buchstabFunction_eq_inv hu hu2, hlogxEq]
      field_simp
    rw [hmain]
    simpa [mul_div_assoc] using hbase x y hy hroot hyx
  have hstep : forall m : Nat, 2 <= m -> P m -> P (m + 1) := by
    intro m hm hPm
    obtain ⟨C, hC, ih⟩ := hPm
    let K : Real := 4 * Real.log 4 *
      ((3 / 2 : Real) + (Real.log 2)⁻¹)
    let Cnext : Real := C * (1 + K) +
      (B + 4 + Real.log 4) * ((m : Real) + 1) ^ 2
    have hCnext : 0 < Cnext := by
      dsimp [Cnext, K]
      positivity
    refine ⟨Cnext, hCnext, ?_⟩
    exact buchstabPhi_error_succ hm hC hB ih
      (fun x u hx hmu hu hlower =>
        hweight m x u hx hm hmu hu hlower)
  intro N hN
  exact Nat.le_induction (P := fun n _ => P n) hbaseP hstep N hN

/-- Montgomery--Vaughan Theorem 7.11 in an explicit compact-uniform form. -/
theorem buchstabPhi_estimate :
    forall U : Real, 1 <= U ->
      exists C : Real, 0 < C ∧
        forall x y u : Real, 0 < x -> 2 <= y -> 1 <= u -> u <= U ->
          u = Real.log x / Real.log y ->
          |(buchstabPhi x y : Real) -
            (buchstabFunction u * x / Real.log y - y / Real.log y)| <=
            C * (x / Real.log x ^ 2) := by
  intro U hU
  let N : Nat := max 2 (Nat.ceil U)
  have hN : 2 <= N := by
    dsimp [N]
    exact Nat.le_max_left 2 (Nat.ceil U)
  obtain ⟨C, hC, hNat⟩ := exists_buchstabPhi_error_nat N hN
  refine ⟨C, hC, ?_⟩
  intro x y u hx hy hu huU heq
  apply hNat x y u hx hy hu _ heq
  have hUceil : U <= (Nat.ceil U : Real) := Nat.le_ceil U
  have hceilN : Nat.ceil U <= N := by
    dsimp [N]
    exact Nat.le_max_right 2 (Nat.ceil U)
  have hceilNReal : (Nat.ceil U : Real) <= (N : Real) := by
    exact_mod_cast hceilN
  exact huU.trans (hUceil.trans hceilNReal)

end PrimesRestrictedDigits
