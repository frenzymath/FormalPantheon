import Waring.Analytic.FourierCoefficientBounds

/-!
# Sum of interval Fourier coefficients

This file performs the finite residue pairing and harmonic comparison in
Chen's Lemma 6 [CHEN1964-EN, p. 1551, equation (8)].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- Residues at a fixed least absolute distance from zero. -/
def leastResidueFiber (q d : Nat) [NeZero q] : Finset (ZMod q) :=
  Finset.univ.filter (fun h ↦ h.valMinAbs.natAbs = d)

/-- A positive least-residue fiber is contained in the pair `d,-d`. -/
theorem card_leastResidueFiber_le_two {q d : Nat} [NeZero q]
    (hd : d ≤ q / 2) : (leastResidueFiber q d).card ≤ 2 := by
  let a : ZMod q := d
  have ha : a.valMinAbs.natAbs = d := by
    dsimp [a]
    rw [ZMod.valMinAbs_natCast_of_le_half hd]
    simp
  calc
    (leastResidueFiber q d).card ≤ ({a, -a} : Finset (ZMod q)).card := by
      apply Finset.card_le_card
      intro h hh
      have hh' : h.valMinAbs.natAbs = d := by
        simpa [leastResidueFiber] using hh
      have hor : h = a ∨ h = -a :=
        ZMod.natAbs_valMinAbs_eq_natAbs_valMinAbs.mp (hh'.trans ha.symm)
      simp [hor]
    _ ≤ 2 := Finset.card_le_two

/-- At an even midpoint the two signed representatives coincide, so the
least-residue fiber has at most one element. -/
theorem card_leastResidueFiber_le_one_of_twice_eq {q d : Nat} [NeZero q]
    (hdPos : 0 < d) (htwice : 2 * d = q) :
    (leastResidueFiber q d).card ≤ 1 := by
  have hd : d ≤ q / 2 := by omega
  let a : ZMod q := d
  have ha : a.valMinAbs.natAbs = d := by
    dsimp [a]
    rw [ZMod.valMinAbs_natCast_of_le_half hd]
    simp
  have hdq : d < q := by omega
  have hself : -a = a := by
    apply (ZMod.neg_eq_self_iff a).2
    right
    dsimp [a]
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt hdq, htwice]
  calc
    (leastResidueFiber q d).card ≤ ({a} : Finset (ZMod q)).card := by
      apply Finset.card_le_card
      intro h hh
      have hh' : h.valMinAbs.natAbs = d := by
        simpa [leastResidueFiber] using hh
      have hor : h = a ∨ h = -a :=
        ZMod.natAbs_valMinAbs_eq_natAbs_valMinAbs.mp (hh'.trans ha.symm)
      rcases hor with rfl | rfl
      · simp
      · simp [hself]
    _ = 1 := by simp

/-- Reciprocal weight supplied by the pointwise geometric estimate.  At the
zero residue this is zero by the field convention for division by zero. -/
noncomputable def leastResidueWeight (q : Nat) [NeZero q]
    (h : ZMod q) : Real :=
  (q : Real) / (2 * (h.valMinAbs.natAbs : Real))

/-- For an odd modulus, the paired reciprocal weights are bounded by the
corresponding harmonic number. -/
theorem sum_leastResidueWeight_odd (n : Nat) :
    (∑ h : ZMod (2 * n + 1), leastResidueWeight (2 * n + 1) h) ≤
      (2 * n + 1 : Nat) * (harmonic n : Real) := by
  let q : Nat := 2 * n + 1
  haveI : NeZero q := ⟨by dsimp [q]; omega⟩
  let distance : ZMod q → Nat := fun h ↦ h.valMinAbs.natAbs
  have hqHalf : q / 2 = n := by dsimp [q]; omega
  have hmap : ∀ h ∈ (Finset.univ : Finset (ZMod q)),
      distance h ∈ Finset.Icc 0 n := by
    intro h _
    simp only [Finset.mem_Icc, Nat.zero_le, true_and]
    rw [← hqHalf]
    exact ZMod.natAbs_valMinAbs_le h
  change (∑ h : ZMod q, leastResidueWeight q h) ≤
    (q : Real) * (harmonic n : Real)
  simp only [leastResidueWeight]
  rw [← Finset.sum_fiberwise_of_maps_to' hmap
    (fun d ↦ (q : Real) / (2 * (d : Real)))]
  calc
    (∑ d ∈ Finset.Icc 0 n,
        ∑ _h ∈ (Finset.univ : Finset (ZMod q)) with distance _h = d,
          (q : Real) / (2 * (d : Real))) ≤
        ∑ d ∈ Finset.Icc 0 n, (q : Real) / d := by
      refine Finset.sum_le_sum (fun d hd ↦ ?_)
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hdHalf : d ≤ q / 2 := by
        rw [hqHalf]
        exact (Finset.mem_Icc.mp hd).2
      have hcard :
          ((Finset.univ : Finset (ZMod q)).filter (fun h ↦ distance h = d)).card ≤ 2 := by
        simpa [leastResidueFiber, distance] using
          (card_leastResidueFiber_le_two (q := q) (d := d) hdHalf)
      have hcardReal :
          (((Finset.univ : Finset (ZMod q)).filter
            (fun h ↦ distance h = d)).card : Real) ≤ 2 := by exact_mod_cast hcard
      calc
        (((Finset.univ : Finset (ZMod q)).filter
              (fun h ↦ distance h = d)).card : Real) *
            ((q : Real) / (2 * (d : Real))) ≤
            2 * ((q : Real) / (2 * (d : Real))) :=
          mul_le_mul_of_nonneg_right hcardReal (by positivity)
        _ = (q : Real) / d := by ring
    _ = (q : Real) * (harmonic n : Real) := by
      rw [← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le n)]
      rw [Finset.sum_insert (by simp)]
      simp only [Nat.cast_zero, div_zero, zero_add]
      rw [harmonic_eq_sum_Icc]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring

/-- For an even modulus, the self-paired midpoint contributes one additional
unit beyond the paired harmonic sum. -/
theorem sum_leastResidueWeight_even (n : Nat) :
    (∑ h : ZMod (2 * (n + 1)), leastResidueWeight (2 * (n + 1)) h) ≤
      (2 * (n + 1) : Nat) * (harmonic n : Real) + 1 := by
  let q : Nat := 2 * (n + 1)
  haveI : NeZero q := ⟨by dsimp [q]; omega⟩
  let distance : ZMod q → Nat := fun h ↦ h.valMinAbs.natAbs
  have hqHalf : q / 2 = n + 1 := by dsimp [q]; omega
  have hmap : ∀ h ∈ (Finset.univ : Finset (ZMod q)),
      distance h ∈ Finset.Icc 0 (n + 1) := by
    intro h _
    simp only [Finset.mem_Icc, Nat.zero_le, true_and]
    rw [← hqHalf]
    exact ZMod.natAbs_valMinAbs_le h
  change (∑ h : ZMod q, leastResidueWeight q h) ≤
    (q : Real) * (harmonic n : Real) + 1
  simp only [leastResidueWeight]
  rw [← Finset.sum_fiberwise_of_maps_to' hmap
    (fun d ↦ (q : Real) / (2 * (d : Real)))]
  rw [← Finset.insert_Icc_right_eq_Icc_add_one (Nat.zero_le (n + 1))]
  rw [Finset.sum_insert (by simp)]
  have hmidCard :
      ((Finset.univ : Finset (ZMod q)).filter
        (fun h ↦ distance h = n + 1)).card ≤ 1 := by
    simpa [leastResidueFiber, distance] using
      (card_leastResidueFiber_le_one_of_twice_eq (q := q) (d := n + 1)
        (by omega) (by dsimp [q]))
  have hmidCardReal :
      (((Finset.univ : Finset (ZMod q)).filter
        (fun h ↦ distance h = n + 1)).card : Real) ≤ 1 := by
    exact_mod_cast hmidCard
  have hmid :
      (∑ _h ∈ (Finset.univ : Finset (ZMod q)) with distance _h = n + 1,
        (q : Real) / (2 * ((n + 1 : Nat) : Real))) ≤ 1 := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    calc
      (((Finset.univ : Finset (ZMod q)).filter
            (fun h ↦ distance h = n + 1)).card : Real) *
          ((q : Real) / (2 * ((n + 1 : Nat) : Real))) ≤
          1 * ((q : Real) / (2 * ((n + 1 : Nat) : Real))) :=
        mul_le_mul_of_nonneg_right hmidCardReal (by positivity)
      _ = 1 := by
        dsimp [q]
        field_simp
        push_cast
        ring
  have hlower :
      (∑ d ∈ Finset.Icc 0 n,
        ∑ _h ∈ (Finset.univ : Finset (ZMod q)) with distance _h = d,
          (q : Real) / (2 * (d : Real))) ≤
        ∑ d ∈ Finset.Icc 0 n, (q : Real) / d := by
    refine Finset.sum_le_sum (fun d hd ↦ ?_)
    simp only [Finset.sum_const, nsmul_eq_mul]
    have hdHalf : d ≤ q / 2 := by
      rw [hqHalf]
      exact (Finset.mem_Icc.mp hd).2.trans (Nat.le_succ n)
    have hcard :
        ((Finset.univ : Finset (ZMod q)).filter
          (fun h ↦ distance h = d)).card ≤ 2 := by
      simpa [leastResidueFiber, distance] using
        (card_leastResidueFiber_le_two (q := q) (d := d) hdHalf)
    have hcardReal :
        (((Finset.univ : Finset (ZMod q)).filter
          (fun h ↦ distance h = d)).card : Real) ≤ 2 := by exact_mod_cast hcard
    calc
      (((Finset.univ : Finset (ZMod q)).filter
            (fun h ↦ distance h = d)).card : Real) *
          ((q : Real) / (2 * (d : Real))) ≤
          2 * ((q : Real) / (2 * (d : Real))) :=
        mul_le_mul_of_nonneg_right hcardReal (by positivity)
      _ = (q : Real) / d := by ring
  calc
    (∑ _h ∈ (Finset.univ : Finset (ZMod q)) with distance _h = n + 1,
          (q : Real) / (2 * ((n + 1 : Nat) : Real))) +
        ∑ d ∈ Finset.Icc 0 n,
          ∑ _h ∈ (Finset.univ : Finset (ZMod q)) with distance _h = d,
            (q : Real) / (2 * (d : Real)) ≤
        1 + ∑ d ∈ Finset.Icc 0 n, (q : Real) / d := add_le_add hmid hlower
    _ = (q : Real) * (harmonic n : Real) + 1 := by
      rw [← Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le n)]
      rw [Finset.sum_insert (by simp)]
      simp only [Nat.cast_zero, div_zero, zero_add]
      rw [harmonic_eq_sum_Icc]
      push_cast
      rw [Finset.mul_sum]
      rw [add_comm]
      apply congrArg (fun z : Real ↦ z + 1)
      apply Finset.sum_congr rfl
      intro d hd
      ring

/-- The reciprocal least-residue weights have total mass at most `q log q`
for every positive modulus. -/
theorem sum_leastResidueWeight_le_log (q : Nat) [NeZero q] :
    (∑ h : ZMod q, leastResidueWeight q h) ≤
      (q : Real) * Real.log q := by
  rcases q.even_or_odd' with ⟨n, hq | hq⟩
  · subst q
    cases n with
    | zero =>
        have hne : 2 * 0 ≠ 0 := NeZero.ne (2 * 0)
        exact (hne rfl).elim
    | succ n =>
        have hqPos : (0 : Real) ≤ (2 * (n + 1) : Nat) := by positivity
        calc
          (∑ h : ZMod (2 * (n + 1)),
              leastResidueWeight (2 * (n + 1)) h) ≤
              (2 * (n + 1) : Nat) * (harmonic n : Real) + 1 :=
            sum_leastResidueWeight_even n
          _ = ((2 * (n + 1) : Nat) : Real) *
                ((harmonic n : Real) +
                  ((2 * (n + 1) : Nat) : Real)⁻¹) := by
            field_simp
          _ ≤ ((2 * (n + 1) : Nat) : Real) *
                Real.log ((2 * (n + 1) : Nat) : Real) :=
            mul_le_mul_of_nonneg_left
              (harmonic_add_even_midpoint_le_log n) hqPos
  · subst q
    calc
      (∑ h : ZMod (2 * n + 1), leastResidueWeight (2 * n + 1) h) ≤
          (2 * n + 1 : Nat) * (harmonic n : Real) :=
        sum_leastResidueWeight_odd n
      _ ≤ ((2 * n + 1 : Nat) : Real) *
          Real.log ((2 * n + 1 : Nat) : Real) :=
        mul_le_mul_of_nonneg_left
          (by
            calc
              (harmonic n : Real) ≤ Real.log (2 * (n : Real) + 1) :=
                harmonic_le_log_two_mul_add_one n
              _ = Real.log ((2 * n + 1 : Nat) : Real) := by
                congr 1
                push_cast
                norm_num)
          (by positivity)

/-- The `L1` norm of the interval Fourier coefficients is bounded by the
modulus times `log q + 1`. -/
theorem sum_norm_intervalFourierCoefficient_le (q : Nat) [NeZero q]
    (M : Int) (m : Nat) (hm : m ≤ q) :
    (∑ h : ZMod q, ‖intervalFourierCoefficient M m h‖) ≤
      (q : Real) * (Real.log q + 1) := by
  let residues : Finset (ZMod q) := Finset.univ
  have hzero : (0 : ZMod q) ∈ residues := by simp [residues]
  rw [← Finset.sum_erase_add residues
    (fun h ↦ ‖intervalFourierCoefficient M m h‖) hzero]
  have hnonzero :
      (∑ h ∈ residues.erase 0, ‖intervalFourierCoefficient M m h‖) ≤
        ∑ h ∈ residues.erase 0, leastResidueWeight q h := by
    apply Finset.sum_le_sum
    intro h hh
    exact norm_intervalFourierCoefficient_le_leastResidue M m
      (Finset.ne_of_mem_erase hh)
  have hzeroBound : ‖intervalFourierCoefficient M m (0 : ZMod q)‖ ≤ m :=
    norm_intervalFourierCoefficient_le_length M m 0
  have hweightZero : leastResidueWeight q (0 : ZMod q) = 0 := by
    simp [leastResidueWeight]
  have hweightSplit :
      (∑ h ∈ residues.erase 0, leastResidueWeight q h) =
        ∑ h : ZMod q, leastResidueWeight q h := by
    rw [← Finset.sum_erase_add residues (leastResidueWeight q) hzero]
    simp only [hweightZero, add_zero]
  have hmReal : (m : Real) ≤ q := by exact_mod_cast hm
  calc
    (∑ h ∈ residues.erase 0, ‖intervalFourierCoefficient M m h‖) +
          ‖intervalFourierCoefficient M m (0 : ZMod q)‖ ≤
        (∑ h ∈ residues.erase 0, leastResidueWeight q h) + m :=
      add_le_add hnonzero hzeroBound
    _ = (m : Real) + ∑ h : ZMod q, leastResidueWeight q h := by
      rw [hweightSplit]
      ring
    _ ≤ (q : Real) + (q : Real) * Real.log q :=
      add_le_add hmReal (sum_leastResidueWeight_le_log q)
    _ = (q : Real) * (Real.log q + 1) := by ring

/-- Equation (8) in conditional form: a uniform completed-sum bound `B`
implies the same incomplete-sum bound with factor `log q + 1`. -/
theorem norm_shortPowerSum_le_log_of_complete_bound
    (q : Nat) [NeZero q] (a : ZMod q) (M : Int) (m : Nat) (B : Real)
    (hm : m ≤ q)
    (hcomplete : ∀ h : ZMod q,
      ‖polynomialCompleteSum a 0 0 0 h‖ ≤ B) :
    ‖shortPowerSum a M m‖ ≤ (Real.log q + 1) * B := by
  have hB : 0 ≤ B :=
    (norm_nonneg (polynomialCompleteSum a 0 0 0 (0 : ZMod q))).trans
      (hcomplete 0)
  have hq : (q : Real) ≠ 0 := by exact_mod_cast NeZero.ne q
  calc
    ‖shortPowerSum a M m‖ ≤
        (q : Real)⁻¹ *
          (∑ h : ZMod q, ‖intervalFourierCoefficient M m h‖) * B :=
      norm_shortPowerSum_le q a M m B hcomplete
    _ ≤ (q : Real)⁻¹ * ((q : Real) * (Real.log q + 1)) * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      exact mul_le_mul_of_nonneg_left
        (sum_norm_intervalFourierCoefficient_le q M m hm) (by positivity)
    _ = (Real.log q + 1) * B := by
      field_simp

-- The weight keeps the nonzero-modulus contract shared by all Fourier bounds,
-- even though its zero-safe quotient formula itself is defined for `q = 0`.
attribute [nolint unusedArguments] leastResidueWeight

end Waring.Analytic
