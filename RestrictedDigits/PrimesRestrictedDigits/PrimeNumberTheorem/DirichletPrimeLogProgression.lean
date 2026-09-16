import PrimesRestrictedDigits.BasicEstimates.PrimeDistribution
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletProgressionLogPower

/-!
# Strict prime-log progression estimates

This transfers the repaired global von Mangoldt progression theorem to the
strict prime-log carrier used in `MAYNARD-PRD-PUBLISHED`, Eq. (11.2) and the
M3 calculation on pp. 186--189.
-/

open scoped BigOperators
open Filter

namespace PrimesRestrictedDigits

/-- The prime-log sum in one residue class under a strict real cutoff. -/
noncomputable def primeLogProgressionSum
    (q a : Nat) (x : Real) : Real :=
  ∑ p ∈ (naturalLeftClosedRightOpenInterval 0 x).filter
      (fun p => p.Prime ∧ p ≡ a [MOD q]),
    Real.log (p : Real)

/-- Independent modulus and error log powers give a uniform strict prime-log
progression estimate. -/
theorem exists_abs_primeLogProgressionSum_sub_main_log_pow_le
    (H B : Nat) :
    ∃ C x0 : Real,
      0 < C ∧ 4 <= x0 ∧
      ∀ x : Real, x0 <= x ->
        ∀ q : Nat, 0 < q -> IsDecimalSmooth q ->
          ∀ a : Nat, Nat.Coprime a q ->
            (q : Real) <= Real.log x ^ B ->
            abs (primeLogProgressionSum q a x -
              x / (q.totient : Real)) <=
                C * x / Real.log x ^ H := by
  obtain ⟨C0, xBase, hC0, hxBase, hGlobal⟩ :=
    exists_abs_vonMangoldtProgressionSum_sub_main_log_pow_le H B
  have hRootEvent :
      ∀ᶠ x : Real in atTop,
        Real.log x ^ (H + 1) <= Real.sqrt x := by
    have hbound :=
      (Real.isLittleO_pow_log_id_atTop (n := 2 * (H + 1))).bound zero_lt_one
    filter_upwards [hbound, eventually_ge_atTop (1 : Real)] with x hx hx1
    have hlogNonneg : 0 <= Real.log x := Real.log_nonneg hx1
    have hxNonneg : 0 <= x := zero_le_one.trans hx1
    have hpowNonneg : 0 <= Real.log x ^ (H + 1) :=
      pow_nonneg hlogNonneg _
    have hsqrtNonneg : 0 <= Real.sqrt x := Real.sqrt_nonneg x
    have hlarge : Real.log x ^ (2 * (H + 1)) <= x := by
      have hleft : 0 <= Real.log x ^ (2 * (H + 1)) :=
        pow_nonneg hlogNonneg _
      simpa only [id_eq, Real.norm_of_nonneg hleft,
        Real.norm_of_nonneg hxNonneg, one_mul] using hx
    have hsquare : (Real.log x ^ (H + 1)) ^ 2 =
        Real.log x ^ (2 * (H + 1)) := by
      rw [← pow_mul]
      congr 1
      omega
    have hsqrtSquare : Real.sqrt x ^ 2 = x := Real.sq_sqrt hxNonneg
    nlinarith
  obtain ⟨XRoot, hXRoot⟩ := eventually_atTop.mp hRootEvent
  let x0 := max xBase XRoot
  refine ⟨C0 + 3, x0, by positivity,
    hxBase.trans (le_max_left _ _), ?_⟩
  intro x hx q hq hSmooth a ha hqlog
  have hBase : xBase <= x := (le_max_left xBase XRoot).trans hx
  have hRootThreshold : XRoot <= x :=
    (le_max_right xBase XRoot).trans hx
  have hxFour : 4 <= x := hxBase.trans hBase
  have hxOne : 1 <= x := by linarith
  have hxNonneg : 0 <= x := by linarith
  have hLogPos : 0 < Real.log x := log_pos_of_four_le hxFour
  have hLogPowPos : 0 < Real.log x ^ H := pow_pos hLogPos H
  have hLogRoot : Real.log x ^ (H + 1) <= Real.sqrt x :=
    hXRoot x hRootThreshold
  have hSqrtLe : Real.sqrt x <= x := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by nlinarith⟩
  have hEndpointScale : Real.log x <= x / Real.log x ^ H := by
    rw [le_div_iff₀ hLogPowPos]
    calc
      Real.log x * Real.log x ^ H = Real.log x ^ (H + 1) :=
        (pow_succ' (Real.log x) H).symm
      _ <= Real.sqrt x := hLogRoot
      _ <= x := hSqrtLe
  have hPrimePowerScale :
      2 * Real.sqrt x * Real.log x <=
        2 * x / Real.log x ^ H := by
    rw [le_div_iff₀ hLogPowPos]
    calc
      (2 * Real.sqrt x * Real.log x) * Real.log x ^ H =
          2 * Real.sqrt x * Real.log x ^ (H + 1) := by
        rw [pow_succ']
        ring
      _ <= 2 * Real.sqrt x * Real.sqrt x := by gcongr
      _ = 2 * x := by nlinarith [Real.mul_self_sqrt hxNonneg]
  let P : Nat -> Prop := fun n => n ≡ a [MOD q]
  let s := (Finset.Ioc 0 (Nat.floor x)).filter P
  have hremove := abs_sum_vonMangoldt_sub_sum_prime_log_le hxOne s
    (Finset.filter_subset _ _)
  have hendpoint := abs_sum_log_naturalClosedInterval_sub_halfOpen_le_log
    (fun n => P n ∧ n.Prime) 0 hxOne
  have hremove' :
      abs (vonMangoldtProgressionSum q a x -
        ∑ p ∈ s with p.Prime, Real.log (p : Real)) <=
          2 * Real.sqrt x * Real.log x := by
    simpa [s, P, vonMangoldtProgressionSum] using hremove
  have hcarrier :
      (naturalClosedInterval 0 x).filter (fun n => P n ∧ n.Prime) =
        s.filter Nat.Prime := by
    dsimp [s]
    ext n
    simp only [naturalClosedInterval, Nat.ceil_zero, Finset.mem_filter,
      Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨_hn0, hnx⟩, hP, hprime⟩
      exact ⟨⟨⟨hprime.pos, hnx⟩, hP⟩, hprime⟩
    · rintro ⟨⟨⟨_hn0, hnx⟩, hP⟩, hprime⟩
      exact ⟨⟨Nat.zero_le n, hnx⟩, hP, hprime⟩
  have hclosedEq :
      (∑ n ∈ (naturalClosedInterval 0 x).filter
          (fun n => P n ∧ n.Prime), Real.log (n : Real)) =
        ∑ p ∈ s with p.Prime, Real.log (p : Real) := by
    rw [hcarrier]
  have hendpoint' :
      abs ((∑ p ∈ s with p.Prime, Real.log (p : Real)) -
        primeLogProgressionSum q a x) <= Real.log x := by
    rw [← hclosedEq]
    simpa [P, primeLogProgressionSum, Finset.filter_filter,
      and_assoc, and_left_comm, and_comm] using hendpoint
  have htransfer :
      abs (vonMangoldtProgressionSum q a x -
        primeLogProgressionSum q a x) <=
          2 * Real.sqrt x * Real.log x + Real.log x := by
    calc
      abs (vonMangoldtProgressionSum q a x -
          primeLogProgressionSum q a x) =
        abs ((vonMangoldtProgressionSum q a x -
          ∑ p ∈ s with p.Prime, Real.log (p : Real)) +
        ((∑ p ∈ s with p.Prime, Real.log (p : Real)) -
          primeLogProgressionSum q a x)) := by ring_nf
      _ <= abs (vonMangoldtProgressionSum q a x -
          ∑ p ∈ s with p.Prime, Real.log (p : Real)) +
        abs ((∑ p ∈ s with p.Prime, Real.log (p : Real)) -
          primeLogProgressionSum q a x) := abs_add_le _ _
      _ <= 2 * Real.sqrt x * Real.log x + Real.log x :=
        add_le_add hremove' hendpoint'
  have hGlobalError := hGlobal x hBase q hq hSmooth a ha hqlog
  calc
    abs (primeLogProgressionSum q a x - x / (q.totient : Real)) =
      abs ((primeLogProgressionSum q a x -
        vonMangoldtProgressionSum q a x) +
        (vonMangoldtProgressionSum q a x -
          x / (q.totient : Real))) := by ring_nf
    _ <= abs (primeLogProgressionSum q a x -
          vonMangoldtProgressionSum q a x) +
        abs (vonMangoldtProgressionSum q a x -
          x / (q.totient : Real)) := abs_add_le _ _
    _ <= (2 * Real.sqrt x * Real.log x + Real.log x) +
        C0 * x / Real.log x ^ H := by
      gcongr
      simpa [abs_sub_comm] using htransfer
    _ <= (2 * x / Real.log x ^ H + x / Real.log x ^ H) +
        C0 * x / Real.log x ^ H := by gcongr
    _ = (C0 + 3) * x / Real.log x ^ H := by ring

end PrimesRestrictedDigits
