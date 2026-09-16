import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Primorial

/-!
# Elementary upper bound for the decimal sieve product

The finite harmonic Euler product gives the one-sided estimate needed in the proof of
Maynard's Lemma 7.4.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

private noncomputable def natReciprocalMonoidHom : Nat →* Real :=
  (invMonoidHom : Real →* Real).comp (Nat.castRingHom Real).toMonoidHom

private theorem interval_mem_factored {N n : Nat}
    (hn : n ∈ Finset.Icc 1 N) :
    n ∈ Nat.factoredNumbers (Nat.primesLE N) := by
  have hnbounds := Finset.mem_Icc.mp hn
  rw [Nat.mem_factoredNumbers']
  intro p hp hpd
  exact Nat.mem_primesLE.mpr
    ⟨Nat.le_trans (Nat.le_of_dvd (by omega) hpd) hnbounds.2, hp⟩

private noncomputable def intervalToFactored (N : Nat) :
    ↑(Finset.Icc 1 N) ↪ Nat.factoredNumbers (Nat.primesLE N) where
  toFun n := ⟨n, interval_mem_factored n.property⟩
  inj' _x _y h := Subtype.ext (congrArg
    (fun z : Nat.factoredNumbers (Nat.primesLE N) ↦ (z : Nat)) h)

private theorem harmonic_le_inverse_primeProduct (N : Nat) :
    (harmonic N : Real) ≤
      (∏ p ∈ Nat.primesLE N, (1 - (p : Real)⁻¹))⁻¹ := by
  let f := natReciprocalMonoidHom
  have hEuler :=
    EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
      (f := f) (fun {p} hp ↦ by
        change ‖((p : Real)⁻¹)‖ < 1
        have hpReal : (0 : Real) < p := by exact_mod_cast hp.pos
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpReal)]
        exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt))
      (Nat.primesLE N)
  let t : Finset (Nat.factoredNumbers (Nat.primesLE N)) :=
    (Finset.Icc 1 N).attach.map (intervalToFactored N)
  calc
    (harmonic N : Real) = ∑ n ∈ Finset.Icc 1 N, (n : Real)⁻¹ := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast]
    _ = ∑ m ∈ t, f m := by
      dsimp [t]
      rw [Finset.sum_map]
      change (∑ n ∈ Finset.Icc 1 N, (n : Real)⁻¹) =
        ∑ x ∈ (Finset.Icc 1 N).attach, ((x : Nat) : Real)⁻¹
      exact (Finset.sum_attach (Finset.Icc 1 N)
        (fun n : Nat ↦ (n : Real)⁻¹)).symm
    _ ≤ ∑' m : Nat.factoredNumbers (Nat.primesLE N), f m := by
      exact hEuler.1.of_norm.sum_le_tsum t (fun m hm ↦ by
        change 0 ≤ ((m : Nat) : Real)⁻¹
        positivity)
    _ = (∏ p ∈ Nat.primesLE N, (1 - (p : Real)⁻¹))⁻¹ := by
      rw [hEuler.2.tsum_eq]
      have hfilter : (Nat.primesLE N).filter Nat.Prime = Nat.primesLE N :=
        Finset.filter_eq_self.mpr (fun p hp ↦ (Nat.mem_primesLE.mp hp).2)
      rw [hfilter, ← Finset.prod_inv_distrib]
      rfl

private theorem primeProduct_le_inv_log_add_one (N : Nat) (hN : 1 ≤ N) :
    (∏ p ∈ Nat.primesLE N, (1 - (p : Real)⁻¹)) ≤
      (Real.log (N + 1 : Nat))⁻¹ := by
  let P : Real := ∏ p ∈ Nat.primesLE N, (1 - (p : Real)⁻¹)
  have hP : 0 < P := by
    dsimp [P]
    apply Finset.prod_pos
    intro p hp
    have hpPrime := (Nat.mem_primesLE.mp hp).2
    have hpReal : (1 : Real) < p := by exact_mod_cast hpPrime.one_lt
    exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hpReal)
  have hlog : 0 < Real.log (N + 1 : Nat) := by
    apply Real.log_pos
    exact_mod_cast Nat.lt_add_one_iff.mpr hN
  have hH : 0 < (harmonic N : Real) :=
    hlog.trans_le (log_add_one_le_harmonic N)
  have hHP : (harmonic N : Real) ≤ P⁻¹ :=
    harmonic_le_inverse_primeProduct N
  have hHPmul : (harmonic N : Real) * P ≤ 1 := by
    rw [inv_eq_one_div] at hHP
    exact (le_div_iff₀ hP).mp hHP
  have hPH : P ≤ (harmonic N : Real)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hH).mpr
    nlinarith
  exact hPH.trans
    ((inv_le_inv₀ hH hlog).mpr (log_add_one_le_harmonic N))

private theorem decimalExcludedPrimeProduct_eq (N : Nat) (hN : 5 ≤ N) :
    (∏ p ∈ (Nat.primesLE N).filter (fun p ↦ ¬p ∣ 10),
      (1 - (p : Real)⁻¹)) =
      (5 / 2 : Real) * ∏ p ∈ Nat.primesLE N,
        (1 - (p : Real)⁻¹) := by
  let g : Nat → Real := fun p ↦ 1 - (p : Real)⁻¹
  have hdivFilter :
      (Nat.primesLE N).filter (fun p ↦ p ∣ 10) = {2, 5} := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hpN, hpPrime⟩, hpDiv⟩
      have hpMul : p ∣ 2 * 5 := by
        simpa only [show (2 * 5 : Nat) = 10 by norm_num] using hpDiv
      rcases hpPrime.dvd_mul.mp hpMul with hpTwo | hpFive
      · rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hpTwo with
          hpOne | hpEq
        · exact (hpPrime.ne_one hpOne).elim
        · exact Or.inl hpEq
      · rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hpFive with
          hpOne | hpEq
        · exact (hpPrime.ne_one hpOne).elim
        · exact Or.inr hpEq
    · intro hp
      rcases hp with rfl | rfl
      · exact ⟨⟨le_trans (show 2 ≤ 5 by norm_num) hN, by decide⟩, by norm_num⟩
      · exact ⟨⟨hN, by decide⟩, by norm_num⟩
  have hpartition := Finset.prod_filter_not_mul_prod_filter
    (Nat.primesLE N) (fun p ↦ p ∣ 10) g
  rw [hdivFilter] at hpartition
  norm_num [g] at hpartition ⊢
  nlinarith

/-- The prime product with the decimal primes removed and weak real cutoff. -/
noncomputable def decimalExcludedPrimeProduct (z : Real) : Real :=
  ∏ p ∈ (Nat.primesLE (Nat.floor z)).filter (fun p ↦ ¬p ∣ 10),
    (1 - (p : Real)⁻¹)

/-- Elementary one-sided product estimate used in Maynard's Lemma 7.4. -/
theorem decimalExcludedPrimeProduct_le (z : Real) (hz : 5 ≤ z) :
    decimalExcludedPrimeProduct z ≤ 5 / (2 * Real.log z) := by
  have hz0 : 0 ≤ z := by linarith
  have hN : 5 ≤ Nat.floor z := (Nat.le_floor_iff hz0).mpr hz
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlogN : 0 < Real.log (Nat.floor z + 1 : Nat) := by
    apply Real.log_pos
    exact_mod_cast Nat.lt_add_one_iff.mpr (show 1 ≤ Nat.floor z by omega)
  have hlogLe : Real.log z ≤ Real.log (Nat.floor z + 1 : Nat) := by
    apply Real.log_le_log (by linarith)
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one z).le
  rw [decimalExcludedPrimeProduct, decimalExcludedPrimeProduct_eq _ hN]
  calc
    (5 / 2 : Real) *
        ∏ p ∈ Nat.primesLE (Nat.floor z), (1 - (p : Real)⁻¹) ≤
      (5 / 2 : Real) * (Real.log (Nat.floor z + 1 : Nat))⁻¹ := by
        gcongr
        exact primeProduct_le_inv_log_add_one _ (by omega)
    _ ≤ (5 / 2 : Real) * (Real.log z)⁻¹ := by
      gcongr
    _ = 5 / (2 * Real.log z) := by field_simp

/-- Source-parameter form of `decimalExcludedPrimeProduct_le`. -/
theorem decimalExcludedPrimeProduct_rpow_le
    {X delta : Real} (hX : 1 < X) (_hdelta : 0 < delta)
    (hcutoff : 5 ≤ X ^ delta) :
    decimalExcludedPrimeProduct (X ^ delta) ≤
      5 / (2 * delta * Real.log X) := by
  have h := decimalExcludedPrimeProduct_le (X ^ delta) hcutoff
  rw [Real.log_rpow (by linarith : 0 < X)] at h
  convert h using 1; ring

end PrimesRestrictedDigits
