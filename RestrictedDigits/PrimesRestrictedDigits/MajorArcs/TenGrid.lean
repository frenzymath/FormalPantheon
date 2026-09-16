import PrimesRestrictedDigits.Digits.LocalDensity
import PrimesRestrictedDigits.MajorArcs.M3Residues
import PrimesRestrictedDigits.MajorArcs.MoebiusSupport
import Mathlib.Tactic.NormNum

/-!
# M3 ten-grid and decimal density

This formalizes the exact finite ten-grid calculation on
`MAYNARD-PRD-PUBLISHED`, p. 189. The progression estimate that supplies the
residue errors remains a separate analytic input.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The ten frequencies corresponding to the fractions `c / 10`. -/
def majorArcTenGridFrequencies (X : Nat) : Finset Nat :=
  (Finset.range 10).image fun c => c * (X / 10)

/-- On a positive power-of-ten scale, the nonzero-Moebius part of repaired
M3 is exactly the ten-grid. The full M3 carrier can contain further points
whose canonical denominator has zero Moebius value. -/
theorem majorArcClassThree_nonzeroMoebius_eq_tenGrid
    {X K : Nat} (hK : 0 < K) (hX : X = 10 ^ K)
    {Q : Real} (hQ : 10 ≤ Q) :
    (majorArcClassThreeFrequencies X Q).filter
        (fun a : Nat => ArithmeticFunction.moebius
          (((a : Rat) / (X : Rat)).den) ≠ 0) =
      majorArcTenGridFrequencies X := by
  classical
  subst X
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hK.ne'
  have hpowdiv : 10 ^ (k + 1) / 10 = 10 ^ k := by
    rw [pow_succ]
    omega
  rw [majorArcTenGridFrequencies, hpowdiv]
  ext a
  constructor
  · intro ha
    rcases Finset.mem_filter.mp ha with ⟨haClass, hmu⟩
    rcases Finset.mem_filter.mp haClass with ⟨haRange, hclass⟩
    have haLt : a < 10 ^ (k + 1) := Finset.mem_range.mp haRange
    rcases hclass.exists_reduced_ratio haLt with
      ⟨b, q, hq, hbq, hbCoprime, hqdiv, _, hratio⟩
    have hqden : (((b : Rat) / (q : Rat)).den) = q := by
      have hcopInt : (b : Int).natAbs.Coprime (q : Int).natAbs := by
        simpa using hbCoprime
      have hden := Rat.den_div_eq_of_coprime
        (a := (b : Int)) (b := (q : Int))
        (by exact_mod_cast hq : (0 : Int) < (q : Int)) hcopInt
      have hcast : (b : Rat) / (q : Rat) =
          ((b : Int) : Rat) / ((q : Int) : Rat) := by norm_num
      calc
        ((b : Rat) / (q : Rat)).den =
            (((b : Int) : Rat) / ((q : Int) : Rat)).den :=
          congrArg Rat.den hcast
        _ = q := by exact_mod_cast hden
    have hmuq : ArithmeticFunction.moebius q ≠ 0 := by
      rw [← hqden, ← hratio]
      exact hmu
    have hq10 : q ∣ 10 :=
      dvd_ten_of_moebius_ne_zero_dvd_ten_pow hqdiv hmuq
    let c := b * (10 / q)
    have hquotpos : 0 < 10 / q :=
      Nat.div_pos (Nat.le_of_dvd (by norm_num) hq10) hq
    have hcLt : c < 10 := by
      change b * (10 / q) < 10
      calc
        b * (10 / q) < q * (10 / q) :=
          (Nat.mul_lt_mul_right hquotpos).2 hbq
        _ = 10 := by rw [Nat.mul_comm, Nat.div_mul_cancel hq10]
    have hqRat : (q : Rat) ≠ 0 := by exact_mod_cast hq.ne'
    have hXrat : ((10 ^ (k + 1) : Nat) : Rat) ≠ 0 := by positivity
    have hcrossRat : (a : Rat) * (q : Rat) =
        (b : Rat) * ((10 ^ (k + 1) : Nat) : Rat) :=
      (div_eq_div_iff hXrat hqRat).mp hratio
    have hcrossNat : a * q = b * 10 ^ (k + 1) := by
      exact_mod_cast hcrossRat
    have htarget : (c * 10 ^ k) * q = b * 10 ^ (k + 1) := by
      dsimp [c]
      rw [pow_succ]
      rw [show (b * (10 / q) * 10 ^ k) * q =
          b * ((10 / q) * q) * 10 ^ k by ring]
      rw [Nat.div_mul_cancel hq10]
      ring
    rw [Finset.mem_image]
    exact ⟨c, Finset.mem_range.mpr hcLt,
      Nat.eq_of_mul_eq_mul_right hq (hcrossNat.trans htarget.symm) |>.symm⟩
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨c, hcRange, rfl⟩
    have hcLt : c < 10 := Finset.mem_range.mp hcRange
    let X := 10 ^ (k + 1)
    let a := c * 10 ^ k
    let r : Rat := (a : Rat) / (X : Rat)
    have haLt : a < X := by
      dsimp [a, X]
      rw [pow_succ]
      have hmul : c * 10 ^ k < 10 * 10 ^ k :=
        (Nat.mul_lt_mul_right (by positivity : 0 < 10 ^ k)).2 hcLt
      omega
    have hratio : r = (c : Rat) / (10 : Rat) := by
      dsimp [r, a, X]
      rw [pow_succ]
      push_cast
      field_simp
    have hden10 : r.den ∣ 10 := by
      rw [hratio]
      have heq : (c : Rat) / (10 : Rat) =
          Rat.divInt (c : Int) (10 : Int) := by
        rw [Rat.divInt_eq_div]
        norm_num
      rw [heq]
      exact_mod_cast Rat.den_dvd (c : Int) (10 : Int)
    have hdenLe : r.den ≤ 10 := Nat.le_of_dvd (by norm_num) hden10
    have hdenX : r.den ∣ X := by
      apply hden10.trans
      dsimp [X]
      exact dvd_pow_self 10 (by omega)
    have happrox : majorArcRationalApproximation X a Q r := by
      refine ⟨?_, ?_⟩
      · dsimp [r]
        simp
        positivity
      · exact (by exact_mod_cast hdenLe : (r.den : Real) ≤ 10).trans hQ
    have hclass : majorArcClassThree X a Q :=
      ⟨r, happrox, hdenX, rfl⟩
    have hsquarefreeTen : Squarefree (10 : Nat) := by
      rw [show (10 : Nat) = 2 * 5 by norm_num, squarefree_mul_iff]
      exact ⟨Nat.coprime_iff_isRelPrime.mp (by norm_num),
        Nat.prime_two.prime.squarefree, Nat.prime_five.prime.squarefree⟩
    have hmu : ArithmeticFunction.moebius r.den ≠ 0 :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr
        (Squarefree.squarefree_of_dvd hden10 hsquarefreeTen)
    rw [Finset.mem_filter]
    constructor
    · rw [majorArcClassThreeFrequencies, Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr (by simpa [a, X] using haLt),
        by simpa [a, X] using hclass⟩
    · simpa [r, a, X] using hmu

/-- Complete orthogonality of the ten decimal phases. -/
theorem majorArcPhase_sum_ten (m n : Nat) :
    (∑ c ∈ Finset.range 10,
      majorArcPhase
        ((c : Real) * (((m : Int) - n : Int) : Real) / 10)) =
      if m ≡ n [MOD 10] then (10 : Complex) else 0 := by
  have hphaseInt (z : Int) : majorArcPhase (z : Real) = 1 := by
    rw [majorArcPhase]
    have harg : (((2 * Real.pi * (z : Real) : Real) : Complex) * Complex.I) =
        (z : Complex) * (2 * (Real.pi : Complex) * Complex.I) := by
      push_cast
      ring
    rw [harg, Complex.exp_int_mul_two_pi_mul_I]
  by_cases hmod : m ≡ n [MOD 10]
  · rw [if_pos hmod]
    rcases Nat.modEq_iff_dvd.mp hmod with ⟨z, hz⟩
    calc
      (∑ c ∈ Finset.range 10,
          majorArcPhase
            ((c : Real) * (((m : Int) - n : Int) : Real) / 10)) =
          ∑ c ∈ Finset.range 10, (1 : Complex) := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [show (c : Real) * (((m : Int) - n : Int) : Real) / 10 =
            ((c : Int) * (-z) : Int) by
          rw [show (m : Int) - n = 10 * (-z) by omega]
          push_cast
          norm_num
          ring]
        exact hphaseInt _
      _ = 10 := by norm_num
  · rw [if_neg hmod]
    have hnotdvd : ¬(10 : Int) ∣ (m : Int) - (n : Int) := by
      intro hdvd
      apply hmod
      apply Nat.modEq_iff_dvd.mpr
      rcases hdvd with ⟨z, hz⟩
      exact ⟨-z, by omega⟩
    have htail := majorArcPhase_sum_Ico_one_eq_neg_one
      (by norm_num : 1 < 10) hnotdvd
    have hsplit := Finset.sum_range_add_sum_Ico
      (fun c : Nat => majorArcPhase
        ((c : Real) * (((m : Int) - n : Int) : Real) / 10))
      (by norm_num : 1 ≤ 10)
    have htail' :
        (∑ c ∈ (Finset.Ico 1 10 : Finset Nat),
          majorArcPhase
            ((c : Real) * (((m : Int) - n : Int) : Real) / 10)) = -1 := by
      simpa using htail
    rw [htail'] at hsplit
    simpa [majorArcPhase] using hsplit.symm

/-- The signed product of digit and weight transforms is the sum of the
matching decimal residue fibers. -/
theorem majorArcTenGrid_bilinear
    (A s : Finset Nat) (w : Nat → Complex) :
    (∑ c ∈ Finset.range 10,
      majorArcWeightedPhaseSum A (fun _ => 1) ((c : Real) / 10) *
        majorArcWeightedPhaseSum s w (-((c : Real) / 10))) =
      10 * ∑ m ∈ A, majorArcResidueWeightSum s w 10 m := by
  classical
  have hphase (c m n : Nat) :
      majorArcPhase ((m : Real) * ((c : Real) / 10)) *
          majorArcPhase ((n : Real) * (-((c : Real) / 10))) =
        majorArcPhase
          ((c : Real) * (((m : Int) - n : Int) : Real) / 10) := by
    rw [majorArcPhase, majorArcPhase, majorArcPhase, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold majorArcWeightedPhaseSum
  simp only [one_mul]
  simp_rw [Finset.sum_mul_sum]
  calc
    (∑ c ∈ Finset.range 10,
        ∑ m ∈ A, ∑ n ∈ s,
          majorArcPhase ((m : Real) * ((c : Real) / 10)) *
            (w n * majorArcPhase ((n : Real) * (-((c : Real) / 10))))) =
        ∑ c ∈ Finset.range 10,
          ∑ m ∈ A, ∑ n ∈ s,
            w n * majorArcPhase
              ((c : Real) * (((m : Int) - n : Int) : Real) / 10) := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      rw [← hphase]
      ring
    _ = ∑ m ∈ A, ∑ n ∈ s,
        w n * ∑ c ∈ Finset.range 10,
          majorArcPhase
            ((c : Real) * (((m : Int) - n : Int) : Real) / 10) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_comm]
    _ = ∑ m ∈ A, ∑ n ∈ s,
        w n * (if m ≡ n [MOD 10] then (10 : Complex) else 0) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      rw [majorArcPhase_sum_ten]
    _ = 10 * ∑ m ∈ A, majorArcResidueWeightSum s w 10 m := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      unfold majorArcResidueWeightSum
      rw [Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hmod : n ≡ m [MOD 10]
      · rw [if_pos hmod, if_pos hmod.symm]
        ring
      · rw [if_neg hmod, if_neg]
        · simp
        · exact fun h => hmod h.symm

private theorem sum_majorArcResidueWeightSum_eq_filter_coprime_ten
    (A s : Finset Nat) (w : Nat → Complex)
    (hsupport : ∀ n ∈ s, w n ≠ 0 → Nat.Coprime n 10) :
    (∑ m ∈ A, majorArcResidueWeightSum s w 10 m) =
      ∑ m ∈ A.filter (fun m => Nat.Coprime m 10),
        majorArcResidueWeightSum s w 10 m := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro m hmA hmnot
  have hmNoncoprime : ¬Nat.Coprime m 10 := by
    intro hmCoprime
    exact hmnot (Finset.mem_filter.mpr ⟨hmA, hmCoprime⟩)
  unfold majorArcResidueWeightSum
  apply Finset.sum_eq_zero
  intro n hn
  rcases Finset.mem_filter.mp hn with ⟨hns, hmod⟩
  by_contra hwn
  apply hmNoncoprime
  rw [Nat.coprime_iff_gcd_eq_one, ← hmod.gcd_eq]
  exact Nat.coprime_iff_gcd_eq_one.mp (hsupport n hns hwn)

/-- After subtracting the decimal local main term, the ten-grid sum is
exactly the sum of its coprime progression errors. -/
theorem majorArcTenGrid_bilinear_sub_density_main
    (a : Fin 10) {K : Nat} (hK : 0 < K)
    (s : Finset Nat) (w : Nat → Complex)
    (hsupport : ∀ n ∈ s, w n ≠ 0 → Nat.Coprime n 10)
    (T : Complex) :
    (∑ c ∈ Finset.range 10,
      majorArcWeightedPhaseSum (paddedRestrictedNumbers a K) (fun _ => 1)
          ((c : Real) / 10) *
        majorArcWeightedPhaseSum s w (-((c : Real) / 10))) -
        (restrictedDigitDensity a : Complex) *
          ((paddedRestrictedNumbers a K).card : Complex) * T =
      10 * ∑ m ∈ (paddedRestrictedNumbers a K).filter
        (fun m => Nat.Coprime m 10),
          (majorArcResidueWeightSum s w 10 m -
            T / (Nat.totient 10 : Complex)) := by
  classical
  let A := paddedRestrictedNumbers a K
  let C := A.filter fun m => Nat.Coprime m 10
  have hprune :
      (∑ m ∈ A, majorArcResidueWeightSum s w 10 m) =
        ∑ m ∈ C, majorArcResidueWeightSum s w 10 m := by
    exact sum_majorArcResidueWeightSum_eq_filter_coprime_ten
      A s w hsupport
  have hdensityRat :=
    ten_div_totient_mul_card_coprime_paddedRestrictedNumbers a hK
  have hdensityCast := congrArg (fun x : Rat => (x : Complex)) hdensityRat
  have hdensity :
      (10 : Complex) / (Nat.totient 10 : Complex) * (C.card : Complex) =
        (restrictedDigitDensity a : Complex) * (A.card : Complex) := by
    simpa [A, C] using hdensityCast
  change
    (∑ c ∈ Finset.range 10,
      majorArcWeightedPhaseSum A (fun _ => 1) ((c : Real) / 10) *
        majorArcWeightedPhaseSum s w (-((c : Real) / 10))) -
        (restrictedDigitDensity a : Complex) * (A.card : Complex) * T =
      10 * ∑ m ∈ C,
        (majorArcResidueWeightSum s w 10 m -
          T / (Nat.totient 10 : Complex))
  rw [majorArcTenGrid_bilinear, hprune, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← hdensity]
  ring

/-- A uniform modulus-ten progression error bounds the complete ten-grid
error with its explicit carrier factor. -/
theorem norm_majorArcTenGrid_bilinear_sub_density_main_le
    (a : Fin 10) {K : Nat} (hK : 0 < K)
    (s : Finset Nat) (w : Nat → Complex)
    (hsupport : ∀ n ∈ s, w n ≠ 0 → Nat.Coprime n 10)
    (T : Complex) {E : Real} (hE : 0 ≤ E)
    (herror : ∀ m ∈ paddedRestrictedNumbers a K,
      Nat.Coprime m 10 →
        ‖majorArcResidueWeightSum s w 10 m -
          T / (Nat.totient 10 : Complex)‖ ≤ E) :
    ‖(∑ c ∈ Finset.range 10,
      majorArcWeightedPhaseSum (paddedRestrictedNumbers a K) (fun _ => 1)
          ((c : Real) / 10) *
        majorArcWeightedPhaseSum s w (-((c : Real) / 10))) -
        (restrictedDigitDensity a : Complex) *
          ((paddedRestrictedNumbers a K).card : Complex) * T‖ ≤
      10 * ((paddedRestrictedNumbers a K).card : Real) * E := by
  classical
  let A := paddedRestrictedNumbers a K
  let C := A.filter fun m => Nat.Coprime m 10
  rw [majorArcTenGrid_bilinear_sub_density_main a hK s w hsupport T]
  change ‖(10 : Complex) * ∑ m ∈ C,
    (majorArcResidueWeightSum s w 10 m -
      T / (Nat.totient 10 : Complex))‖ ≤ 10 * (A.card : Real) * E
  calc
    ‖(10 : Complex) * ∑ m ∈ C,
        (majorArcResidueWeightSum s w 10 m -
          T / (Nat.totient 10 : Complex))‖ =
        10 * ‖∑ m ∈ C,
          (majorArcResidueWeightSum s w 10 m -
            T / (Nat.totient 10 : Complex))‖ := by
      rw [norm_mul]
      norm_num
    _ ≤ 10 * ∑ m ∈ C,
        ‖majorArcResidueWeightSum s w 10 m -
          T / (Nat.totient 10 : Complex)‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ 10 * ∑ _m ∈ C, E := by
      gcongr with m hm
      rcases Finset.mem_filter.mp hm with ⟨hmA, hmCoprime⟩
      exact herror m (by simpa [A] using hmA) hmCoprime
    _ = 10 * (C.card : Real) * E := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ 10 * (A.card : Real) * E := by
      gcongr
      exact Finset.filter_subset _ _

end PrimesRestrictedDigits
