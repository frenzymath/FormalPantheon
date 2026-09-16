import PrimesRestrictedDigits.MajorArcs.Factorization
import PrimesRestrictedDigits.MajorArcs.Partition
import PrimesRestrictedDigits.MajorArcs.RamanujanSum
import PrimesRestrictedDigits.MajorArcs.ResiduePhaseSum
import Mathlib.Tactic.NormNum

/-!
# Exact M3 residue regrouping

This formalizes the finite algebra in the M3 calculation on published
pp. 188--189 and makes explicit the coprimality support suppressed there.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- An exact M3 rational has a canonical reduced natural numerator and
denominator. -/
theorem majorArcClassThree.exists_reduced_ratio
    {X a : Nat} {Q : Real} (ha : a < X)
    (hclass : majorArcClassThree X a Q) :
    ∃ b q : Nat,
      0 < q ∧ b < q ∧ Nat.Coprime b q ∧ q ∣ X ∧
      (q : Real) ≤ Q ∧
      (a : Rat) / (X : Rat) = (b : Rat) / (q : Rat) := by
  rcases hclass.exact with ⟨r, hr, hden, heq⟩
  let b := r.num.natAbs
  let q := r.den
  have hX : 0 < X := by omega
  have hXrat : (0 : Rat) < X := by exact_mod_cast hX
  have haRat : (a : Rat) < X := by exact_mod_cast ha
  have hrnonneg : (0 : Rat) ≤ r := by
    rw [heq]
    positivity
  have hnum : 0 ≤ r.num := Rat.num_nonneg.mpr hrnonneg
  have hrlt : r < 1 := by
    rw [heq]
    exact (div_lt_one hXrat).2 haRat
  have hbq : b < q := by
    change r.num.natAbs < r.den
    have hnumlt : r.num < (r.den : Int) :=
      Rat.num_lt_denom_iff.mpr hrlt
    omega
  have hratio : (b : Rat) / (q : Rat) = r := by
    change (r.num.natAbs : Rat) / (r.den : Rat) = r
    rw [show (r.num.natAbs : Rat) = (r.num : Rat) by
      simp [abs_of_nonneg hnum]]
    exact r.num_div_den
  exact ⟨b, q, r.den_pos, hbq, r.reduced, hden, hr.2,
    heq.symm.trans hratio.symm⟩

private theorem sum_residueWeights_eq_sum_reduced_of_support
    (s : Finset Nat) (w : Nat → Complex) {q : Nat} (b : Int)
    (hsupport : ∀ n ∈ s, w n ≠ 0 → Nat.Coprime n q) :
    (∑ r ∈ Finset.range q,
        majorArcPhase ((b : Real) * (r : Real) / (q : Real)) *
          majorArcResidueWeightSum s w q r) =
      ∑ r ∈ majorArcReducedResidues q,
        majorArcPhase ((b : Real) * (r : Real) / (q : Real)) *
          majorArcResidueWeightSum s w q r := by
  classical
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro r hrange hrnot
  have hnotcoprime : ¬Nat.Coprime r q := by
    intro hcoprime
    exact hrnot (Finset.mem_filter.mpr ⟨hrange, hcoprime⟩)
  rw [mul_eq_zero]
  right
  unfold majorArcResidueWeightSum
  apply Finset.sum_eq_zero
  intro n hn
  rcases Finset.mem_filter.mp hn with ⟨hns, hmod⟩
  by_contra hwn
  have hncoprime := hsupport n hns hwn
  apply hnotcoprime
  rw [Nat.coprime_iff_gcd_eq_one, ← hmod.gcd_eq]
  exact Nat.coprime_iff_gcd_eq_one.mp hncoprime

/-- Residue regrouping may be pruned to reduced residues when the nonzero
weight support is coprime to the modulus. -/
theorem majorArcWeightedPhaseSum_rat_eq_sum_reducedResidues
    (s : Finset Nat) (w : Nat → Complex)
    {q : Nat} (hq : 0 < q) (b : Int)
    (hsupport : ∀ n ∈ s, w n ≠ 0 → Nat.Coprime n q) :
    majorArcWeightedPhaseSum s w ((b : Real) / (q : Real)) =
      ∑ r ∈ majorArcReducedResidues q,
        majorArcPhase ((b : Real) * (r : Real) / (q : Real)) *
          majorArcResidueWeightSum s w q r := by
  rw [majorArcWeightedPhaseSum_rat_eq_sum_residues s w hq b,
    sum_residueWeights_eq_sum_reduced_of_support s w b hsupport]

/-- On the actual M3 power-of-ten carrier, every nonzero region weight is
coprime to every exact denominator dividing `X`. -/
theorem majorArcRegionWeightAtProduct_coprime_of_dvd_powerTen
    {X K q k n : Nat} {a : Fin k → Real} {delta eta : Real}
    (hX : 1 < X) (heta : 0 < eta) (ha : ∀ i, eta / 2 ≤ a i)
    (hlarge : 5 < (X : Real) ^ (eta / 4))
    (hpower : X = 10 ^ K) (hq : q ∣ X)
    (hweight : majorArcRegionWeightAtProduct X a delta eta n ≠ 0) :
    Nat.Coprime n q := by
  have hfiber :
      ((majorArcPrimeTuples X a delta eta).filter
        (fun p => primeTupleProduct p = n)).Nonempty := by
    by_contra hempty
    have heq :
        (majorArcPrimeTuples X a delta eta).filter
            (fun p => primeTupleProduct p = n) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    apply hweight
    unfold majorArcRegionWeightAtProduct primeTupleWeightAtProduct
    rw [heq, Finset.sum_empty]
  rcases hfiber with ⟨p, hp⟩
  rcases Finset.mem_filter.mp hp with ⟨hpTuple, hproduct⟩
  have hpInfo := mem_majorArcPrimeTuples_iff.mp hpTuple
  have primeCoprime {r : Nat} (hr : r.Prime) (hrlarge : 5 < r) :
      Nat.Coprime r q := by
    rw [hr.coprime_iff_not_dvd]
    intro hrq
    have hrpow : r ∣ 10 ^ K := hrq.trans (by simpa [hpower] using hq)
    have hrten : r ∣ 10 := hr.dvd_of_dvd_pow hrpow
    have hrprod : r ∣ 2 * 5 := by
      norm_num at hrten ⊢
      exact hrten
    rcases hr.dvd_mul.mp hrprod with hr2 | hr5
    · have := Nat.le_of_dvd (by norm_num : 0 < 2) hr2
      omega
    · have := Nat.le_of_dvd (by norm_num : 0 < 5) hr5
      omega
  rw [← hproduct, primeTupleProduct,
    Nat.coprime_fintype_prod_left_iff]
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · let r := p (Fin.last k)
    have hrPrime : r.Prime :=
      Nat.prime_of_mem_primesLE (hpInfo.1 (Fin.last k))
    have hlowerLog :
        eta / 4 ≤ normalizedPrimeLog X r :=
      (max_le_iff.mp hpInfo.2.2.2).1
    have hlower :
        (X : Real) ^ (eta / 4) ≤ (r : Real) := by
      have hmax :
          max (eta / 4) (eta / 4) ≤ normalizedPrimeLog X r := by
        simpa using hlowerLog
      exact (max_le_normalizedPrimeLog_iff_rpow_le hX hrPrime
        (eta / 4) (eta / 4)).mp hmax |>.1
    apply primeCoprime hrPrime
    exact_mod_cast hlarge.trans_le hlower
  · let r := p j.castSucc
    have hrPrime : r.Prime :=
      Nat.prime_of_mem_primesLE (hpInfo.1 j.castSucc)
    have hbox :
        normalizedPrimeLog X r ∈ Set.Ioc (a j) (a j + delta) :=
      hpInfo.2.1 j
    have hlower :
        (X : Real) ^ (a j) < (r : Real) :=
      (normalizedPrimeLog_mem_Ioc_iff_rpow hX hrPrime _ _).mp hbox |>.1
    have hexponent : eta / 4 ≤ a j := by
      linarith [ha j, heta]
    have hXone : (1 : Real) ≤ X := by exact_mod_cast hX.le
    have hscale :
        (X : Real) ^ (eta / 4) ≤ (X : Real) ^ (a j) :=
      Real.rpow_le_rpow_of_exponent_le hXone hexponent
    apply primeCoprime hrPrime
    exact_mod_cast hlarge.trans (hscale.trans_lt hlower)

/-- The source region weight therefore admits the reduced-residue
regrouping without an additional bound on the divisor denominator. -/
theorem majorArcRegionWeightedPhaseSum_rat_eq_sum_reducedResidues
    {X K q k : Nat} {a : Fin k → Real} {delta eta : Real}
    (hX : 1 < X) (heta : 0 < eta) (ha : ∀ i, eta / 2 ≤ a i)
    (hlarge : 5 < (X : Real) ^ (eta / 4))
    (hpower : X = 10 ^ K) (hqdiv : q ∣ X) (hq : 0 < q) (b : Int) :
    majorArcWeightedPhaseSum (Finset.range X)
        (fun n => (majorArcRegionWeightAtProduct X a delta eta n : Complex))
        ((b : Real) / (q : Real)) =
      ∑ r ∈ majorArcReducedResidues q,
        majorArcPhase ((b : Real) * (r : Real) / (q : Real)) *
          majorArcResidueWeightSum (Finset.range X)
            (fun n =>
              (majorArcRegionWeightAtProduct X a delta eta n : Complex)) q r := by
  apply majorArcWeightedPhaseSum_rat_eq_sum_reducedResidues _ _ hq b
  intro n hn hnweight
  apply majorArcRegionWeightAtProduct_coprime_of_dvd_powerTen
    hX heta ha hlarge hpower hqdiv
  exact_mod_cast hnweight

/-- Subtracting one common residue main term leaves the exact sum of the
residue errors. In particular, no reduced-residue cardinality is discarded. -/
theorem majorArcWeightedPhaseSum_sub_moebius_main
    (s : Finset Nat) (w : Nat → Complex) {q : Nat} (hq : 0 < q)
    {b : Int} (hb : Nat.Coprime b.natAbs q)
    (hsupport : ∀ n ∈ s, w n ≠ 0 → Nat.Coprime n q)
    (M : Complex) :
    majorArcWeightedPhaseSum s w ((b : Real) / (q : Real)) -
        ((ArithmeticFunction.moebius q : Int) : Complex) * M =
      ∑ r ∈ majorArcReducedResidues q,
        majorArcPhase ((b : Real) * (r : Real) / (q : Real)) *
          (majorArcResidueWeightSum s w q r - M) := by
  rw [majorArcWeightedPhaseSum_rat_eq_sum_reducedResidues s w hq b hsupport,
    ← majorArcRamanujanSum_eq_moebius hq hb]
  unfold majorArcRamanujanSum
  rw [Finset.sum_mul]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]

/-- A pointwise reduced-residue error incurs the full totient factor after
triangle inequality. -/
theorem norm_majorArcWeightedPhaseSum_sub_moebius_main_le_totient
    (s : Finset Nat) (w : Nat → Complex) {q : Nat} (hq : 0 < q)
    {b : Int} (hb : Nat.Coprime b.natAbs q)
    (hsupport : ∀ n ∈ s, w n ≠ 0 → Nat.Coprime n q)
    (M : Complex) {E : Real}
    (herror : ∀ r ∈ majorArcReducedResidues q,
      ‖majorArcResidueWeightSum s w q r - M‖ ≤ E) :
    ‖majorArcWeightedPhaseSum s w ((b : Real) / (q : Real)) -
      ((ArithmeticFunction.moebius q : Int) : Complex) * M‖ ≤
        (Nat.totient q : Real) * E := by
  have hphase (r : Nat) :
      ‖majorArcPhase ((b : Real) * (r : Real) / (q : Real))‖ = 1 := by
    rw [majorArcPhase]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [majorArcWeightedPhaseSum_sub_moebius_main
    s w hq hb hsupport M]
  calc
    ‖∑ r ∈ majorArcReducedResidues q,
        majorArcPhase ((b : Real) * (r : Real) / (q : Real)) *
          (majorArcResidueWeightSum s w q r - M)‖ ≤
        ∑ r ∈ majorArcReducedResidues q,
          ‖majorArcPhase ((b : Real) * (r : Real) / (q : Real)) *
            (majorArcResidueWeightSum s w q r - M)‖ :=
      norm_sum_le _ _
    _ = ∑ r ∈ majorArcReducedResidues q,
        ‖majorArcResidueWeightSum s w q r - M‖ := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [norm_mul, hphase, one_mul]
    _ ≤ ∑ _r ∈ majorArcReducedResidues q, E := by
      gcongr with r hr
      exact herror r hr
    _ = (Nat.totient q : Real) * E := by
      simp [Finset.sum_const, nsmul_eq_mul,
        card_majorArcReducedResidues]

/-- The unit-weight transform is bounded by the size of its finite carrier. -/
theorem norm_majorArcWeightedPhaseSum_one_le_card
    (s : Finset Nat) (theta : Real) :
    ‖majorArcWeightedPhaseSum s (fun _ => 1) theta‖ ≤
      (s.card : Real) := by
  have hphase (n : Nat) :
      ‖majorArcPhase ((n : Real) * theta)‖ = 1 := by
    rw [majorArcPhase]
    exact Complex.norm_exp_ofReal_mul_I _
  unfold majorArcWeightedPhaseSum
  calc
    ‖∑ n ∈ s, (1 : Complex) *
        majorArcPhase ((n : Real) * theta)‖ ≤
        ∑ n ∈ s, ‖(1 : Complex) *
          majorArcPhase ((n : Real) * theta)‖ :=
      norm_sum_le _ _
    _ = ∑ _n ∈ s, (1 : Real) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul, norm_one, hphase, one_mul]
    _ = (s.card : Real) := by simp

end PrimesRestrictedDigits
