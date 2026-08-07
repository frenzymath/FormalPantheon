import BoundedGaps.Maynard.CoprimeHarmonicPrimeAdjunction
import BoundedGaps.Maynard.RoughModulusPrimePredecessorMass

noncomputable section

/-!
# Smooth main term for coprime harmonic sums

The density, Euler constant, and prime-predecessor mass are packaged at a
positive real endpoint. The resulting main term has the same exact prime
adjunction recurrence as the finite coprime harmonic sum.
-/

namespace BoundedGaps.Maynard

noncomputable def coprimeHarmonicDensity (W : ℕ) : ℝ :=
  (Nat.totient W : ℝ) / W

noncomputable def coprimeHarmonicMainTerm (W : ℕ) (x : ℝ) : ℝ :=
  coprimeHarmonicDensity W *
    (Real.log x + Real.eulerMascheroniConstant +
      primeLogPredecessorDivisorMass W)

theorem primeLogPredecessorDivisorMass_primorial_eq
    (D : ℕ) :
    primeLogPredecessorDivisorMass (primorial D) =
      primeLogPredecessorSum D := by
  unfold primeLogPredecessorDivisorMass primeLogPredecessorSum
  rw [primeFactors_primorial]

theorem primeLogPredecessorDivisorMass_mul_prime
    {W p : ℕ} (hW : 0 < W) (hp : p.Prime)
    (hpW : Nat.Coprime p W) :
    primeLogPredecessorDivisorMass (W * p) =
      primeLogPredecessorDivisorMass W +
        Real.log p / (p - 1 : ℕ) := by
  have hpNotMem : p ∉ W.primeFactors := by
    intro hpMem
    have hpdvd := Nat.dvd_of_mem_primeFactors hpMem
    exact (hp.coprime_iff_not_dvd.mp hpW) hpdvd
  have hdisj : Disjoint W.primeFactors ({p} : Finset ℕ) := by
    rw [Finset.disjoint_singleton_right]
    exact hpNotMem
  unfold primeLogPredecessorDivisorMass
  rw [Nat.primeFactors_mul hW.ne' hp.ne_zero, hp.primeFactors,
    Finset.sum_union hdisj, Finset.sum_singleton]

theorem coprimeHarmonicMainTerm_mul_prime
    {W p : ℕ} (hW : 0 < W) (hp : p.Prime)
    (hpW : Nat.Coprime p W) {x : ℝ} (hx : 0 < x) :
    coprimeHarmonicMainTerm (W * p) x =
      coprimeHarmonicMainTerm W x -
        (1 : ℝ) / p * coprimeHarmonicMainTerm W (x / p) := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hmass := primeLogPredecessorDivisorMass_mul_prime hW hp hpW
  have hlog : Real.log (x / p) = Real.log x - Real.log p := by
    rw [Real.log_div hx.ne' hpPos.ne']
  have htotient : Nat.totient (W * p) = Nat.totient W * Nat.totient p :=
    Nat.totient_mul hpW.symm
  have htotientPrime : Nat.totient p = p - 1 := Nat.totient_prime hp
  unfold coprimeHarmonicMainTerm coprimeHarmonicDensity
  rw [htotient, htotientPrime, hmass, hlog]
  rw [Nat.cast_mul]
  rw [Nat.cast_sub hp.one_le]
  norm_num only [Nat.cast_one]
  push_cast
  have hWPos : (0 : ℝ) < W := by exact_mod_cast hW
  have hpPredPos : (0 : ℝ) < (p : ℝ) - 1 := by
    have hpOne : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  field_simp [ne_of_gt hpPos, ne_of_gt hx, ne_of_gt hWPos,
    ne_of_gt hpPredPos]
  ring

end BoundedGaps.Maynard
