import PrimesRestrictedDigits.SieveAsymptotics.SectionSixRecurrenceRanges
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Positivity

/-!
# Fixed-delta factor-length bound for Section 6 states

Every prime factor above `X^delta` consumes at least `delta` of the logarithmic size budget.
This bounds state multiplicity after `delta` is fixed.
-/

namespace PrimesRestrictedDigits

noncomputable section

theorem primeFactorsList_length_real_le_inv_delta
    {X delta : Real} {n : Nat}
    (hX : 1 < X) (hdelta : 0 < delta) (hn : n ≠ 0)
    (hnX : (n : Real) ≤ X)
    (hlower : ∀ q ∈ n.primeFactorsList, X ^ delta ≤ (q : Real)) :
    (n.primeFactorsList.length : Real) ≤ 1 / delta := by
  let factors : List Nat := n.primeFactorsList
  let realFactors : List Real :=
    List.map (fun q : Nat => (q : Real)) factors
  have hfactorLower : ∀ q ∈ realFactors, X ^ delta ≤ q := by
    intro q hq
    rcases List.mem_map.mp hq with ⟨r, hr, rfl⟩
    exact hlower r hr
  have hbaseNonneg : 0 ≤ X ^ delta :=
    Real.rpow_nonneg (zero_lt_one.trans hX).le _
  have hpowProdNat : ∀ l : List Nat,
      (∀ q ∈ l, X ^ delta ≤ (q : Real)) →
      (X ^ delta) ^ l.length ≤
        (List.map (fun q : Nat => (q : Real)) l).prod := by
    intro l
    induction l with
    | nil => simp
    | cons q rest ih =>
        intro hl
        have hhead : X ^ delta ≤ (q : Real) := hl q (by simp)
        have htail : ∀ r ∈ rest, X ^ delta ≤ (r : Real) := by
          intro r hr
          exact hl r (by simp [hr])
        have hmul := mul_le_mul hhead (ih htail)
          (pow_nonneg hbaseNonneg rest.length) (Nat.cast_nonneg q)
        simpa [pow_succ, mul_comm] using hmul
  have hpowProd : (X ^ delta) ^ realFactors.length ≤ realFactors.prod := by
    simpa [realFactors, factors] using
      hpowProdNat n.primeFactorsList hlower
  have hlength : realFactors.length = n.primeFactorsList.length := by
    simp [realFactors, factors]
  have hprod : realFactors.prod = (n : Real) := by
    dsimp [realFactors, factors]
    rw [← Nat.cast_list_prod, Nat.prod_primeFactorsList hn]
  have hpower :
      X ^ (delta * (n.primeFactorsList.length : Real)) ≤ X := by
    calc
      X ^ (delta * (n.primeFactorsList.length : Real)) =
          (X ^ delta) ^ n.primeFactorsList.length := by
        exact Real.rpow_mul_natCast (zero_lt_one.trans hX).le delta
          n.primeFactorsList.length
      _ = (X ^ delta) ^ realFactors.length := by rw [hlength]
      _ ≤ realFactors.prod := hpowProd
      _ = (n : Real) := hprod
      _ ≤ X := hnX
  have hexponent : delta * (n.primeFactorsList.length : Real) ≤ 1 := by
    by_contra hnot
    have hgt : 1 < delta * (n.primeFactorsList.length : Real) :=
      lt_of_not_ge hnot
    have hstrict := (Real.strictMono_rpow_of_base_gt_one hX) hgt
    have hstrict' : X <
        X ^ (delta * (n.primeFactorsList.length : Real)) := by
      simpa only [Real.rpow_one] using hstrict
    exact (not_lt_of_ge hpower) hstrict'
  apply (le_div_iff₀ hdelta).2
  simpa [mul_comm] using hexponent

theorem primeFactorsList_length_le_ceil_inv_delta
    {X delta : Real} {n : Nat}
    (hX : 1 < X) (hdelta : 0 < delta) (hn : n ≠ 0)
    (hnX : (n : Real) ≤ X)
    (hlower : ∀ q ∈ n.primeFactorsList, X ^ delta ≤ (q : Real)) :
    n.primeFactorsList.length ≤ Nat.ceil (1 / delta) := by
  have hreal := primeFactorsList_length_real_le_inv_delta
    hX hdelta hn hnX hlower
  have hceil : (1 / delta) ≤ (Nat.ceil (1 / delta) : Real) := Nat.le_ceil _
  exact_mod_cast hreal.trans hceil

theorem sectionSixRecurrenceState_factorLength_le_ceil_inv_delta
    {band : SectionSixStateBand} {ell n : Nat}
    {X delta theta : Real}
    (hX : 1 < X) (hdelta : 0 < delta)
    (s : SectionSixRecurrenceState band ell n)
    (hnX : (n : Real) ≤ X)
    (houter : ∀ i, X ^ delta ≤ (s.outer i : Real))
    (hinner : sectionSixStateInnerRange X delta theta s.inner) :
    n.primeFactorsList.length ≤ Nat.ceil (1 / delta) := by
  have houterPos : 0 < primeTupleProduct s.outer := by
    rw [primeTupleProduct]
    exact Finset.prod_pos fun i hi => (s.outerPrime i).pos
  have hinnerPos : 0 < s.inner.prod := by
    apply List.prod_pos
    intro q hq
    exact (s.innerPrime q hq).pos
  have hn : n ≠ 0 := by
    rw [← s.product_eq]
    exact Nat.mul_ne_zero houterPos.ne' hinnerPos.ne'
  apply primeFactorsList_length_le_ceil_inv_delta hX hdelta hn hnX
  intro q hqmem
  have hqPrime : q.Prime := Nat.prime_of_mem_primeFactorsList hqmem
  have hqDvd : q ∣ n := ((Nat.mem_primeFactorsList hn).mp hqmem).2
  rw [← s.product_eq] at hqDvd
  rcases hqPrime.dvd_mul.mp hqDvd with hqOuter | hqInner
  · rw [primeTupleProduct] at hqOuter
    rcases (Prime.dvd_finsetProd_iff hqPrime.prime s.outer).mp hqOuter with
      ⟨i, hi, hqi⟩
    have heq : q = s.outer i :=
      (Nat.prime_dvd_prime_iff_eq hqPrime (s.outerPrime i)).mp hqi
    simpa [heq] using houter i
  · rcases (Prime.dvd_prod_iff hqPrime.prime).mp hqInner with
      ⟨r, hr, hqr⟩
    have heq : q = r :=
      (Nat.prime_dvd_prime_iff_eq hqPrime (s.innerPrime r hr)).mp hqr
    subst r
    exact (hinner q hr).1.le

theorem card_sectionSixRecurrenceState_le_five_ceil_inv_delta_pow
    {band : SectionSixStateBand} {ell n : Nat}
    {X delta theta : Real}
    (hX : 1 < X) (hdelta : 0 < delta) (hnX : (n : Real) ≤ X)
    (S : Finset (SectionSixRecurrenceState band ell n))
    (houter : ∀ s ∈ S, ∀ i, X ^ delta ≤ (s.outer i : Real))
    (hinner : ∀ s ∈ S,
      sectionSixStateInnerRange X delta theta s.inner) :
    S.card ≤ 5 * (Nat.ceil (1 / delta)) ^ ell := by
  classical
  by_cases hS : S = ∅
  · simp [hS]
  · obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    have houterPos : 0 < primeTupleProduct s.outer := by
      rw [primeTupleProduct]
      exact Finset.prod_pos fun i hi => (s.outerPrime i).pos
    have hinnerPos : 0 < s.inner.prod := by
      apply List.prod_pos
      intro q hq
      exact (s.innerPrime q hq).pos
    have hn : n ≠ 0 := by
      rw [← s.product_eq]
      exact Nat.mul_ne_zero houterPos.ne' hinnerPos.ne'
    have hlength :=
      sectionSixRecurrenceState_factorLength_le_ceil_inv_delta
        hX hdelta s hnX (houter s hs) (hinner s hs)
    have hcard :=
      card_sectionSixRecurrenceState_le_five_factorLength_pow hn S
    calc
      S.card ≤ 5 * n.primeFactorsList.length ^ ell := hcard
      _ ≤ 5 * (Nat.ceil (1 / delta)) ^ ell := by
        exact Nat.mul_le_mul_left 5 (Nat.pow_le_pow_left hlength ell)

end

end PrimesRestrictedDigits
