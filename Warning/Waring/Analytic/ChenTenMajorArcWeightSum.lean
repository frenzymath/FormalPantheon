import Waring.Analytic.ChenTenArcs
import Mathlib.Analysis.SumIntegralComparisons

/-!
# Summing the Chen major-arc denominator weights

This lightweight module groups reduced arc indices by denominator.  Keeping the
finite-fiber argument separate avoids re-elaborating the large analytic
integrand environment used by the decay estimates.
-/

namespace Waring.Analytic

open Set MeasureTheory
open scoped BigOperators Interval

noncomputable section

/-- The denominator weight in the integrated one-arc error. -/
def chenTenArcWeight (q : Nat) : Real :=
  (q : Real) ^ (-9 / 5 : Real)

/-- The weight left after counting at most `q` reduced numerators. -/
def chenTenReducedArcWeight (q : Nat) : Real :=
  (q : Real) ^ (-4 / 5 : Real)

/-- The finite set of reduced arc indices having a fixed denominator. -/
def chenTenArcDenominatorFiber (P q : Nat) : Finset (ChenTenArcIndex P) :=
  Finset.univ.filter fun i => i.denominator = q

/-- A fixed-denominator arc fiber injects into the reduced residue classes
counted by Euler's totient. -/
theorem card_chenTenArcDenominatorFiber_le_totient (P q : Nat) :
    (chenTenArcDenominatorFiber P q).card <= q.totient := by
  let reducedNumerators :=
    (Finset.range q).filter fun a => q.Coprime a
  have hcard :
      (chenTenArcDenominatorFiber P q).card <= reducedNumerators.card := by
    apply Finset.card_le_card_of_injOn
      (fun i : ChenTenArcIndex P => i.numerator)
    · intro i hi
      have hiq : i.denominator = q := (Finset.mem_filter.mp hi).2
      change i.numerator ∈ reducedNumerators
      simp only [reducedNumerators, Finset.mem_filter, Finset.mem_range]
      constructor
      · simpa [hiq] using i.numerator_lt_denominator
      · simpa [hiq] using i.coprime.symm
    · intro i hi j hj hij
      apply ChenTenArcIndex.ext hij
      have hiq : i.denominator = q := (Finset.mem_filter.mp hi).2
      have hjq : j.denominator = q := (Finset.mem_filter.mp hj).2
      exact hiq.trans hjq.symm
  simpa [reducedNumerators, Nat.totient_eq_card_coprime] using hcard

/-- The finite sum of `q^(-4/5)` through `Q` is at most `5*Q^(1/5)`. -/
theorem sum_range_chenTenReducedArcWeight_le (Q : Nat) (hQ : 1 ≤ Q) :
    (∑ k ∈ Finset.range Q, chenTenReducedArcWeight (k + 1)) <=
      5 * (Q : Real) ^ (1 / 5 : Real) := by
  have hanti : AntitoneOn (fun x : Real => x ^ (-4 / 5 : Real))
      (Set.Icc (1 : Real) (1 + ((Q - 1 : Nat) : Real))) := by
    apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
      (r := -4 / 5) (by norm_num)).mono
    intro x hx
    exact lt_of_lt_of_le (by norm_num) hx.1
  have hsum := AntitoneOn.sum_le_integral (x₀ := (1 : Real))
    (a := Q - 1) hanti
  have hcast : (1 : Real) + ((Q - 1 : Nat) : Real) = (Q : Real) := by
    rw [Nat.cast_sub hQ]
    norm_num
  conv_lhs =>
    rw [show Q = (Q - 1) + 1 by omega, Finset.sum_range_succ']
  calc
    (∑ k ∈ Finset.range (Q - 1), chenTenReducedArcWeight (k + 1 + 1)) +
        chenTenReducedArcWeight (0 + 1) <=
        (∫ x : Real in (1 : Real)..1 + (Q - 1 : Nat),
          x ^ (-4 / 5 : Real)) + 1 := by
      have htail :
          (∑ k ∈ Finset.range (Q - 1),
              chenTenReducedArcWeight (k + 1 + 1)) <=
            ∫ x : Real in (1 : Real)..1 + (Q - 1 : Nat),
              x ^ (-4 / 5 : Real) := by
        calc
          (∑ k ∈ Finset.range (Q - 1),
              chenTenReducedArcWeight (k + 1 + 1)) =
              ∑ k ∈ Finset.range (Q - 1),
                ((1 : Real) + (k + 1 : Nat)) ^ (-4 / 5 : Real) := by
            apply Finset.sum_congr rfl
            intro k hk
            unfold chenTenReducedArcWeight
            congr 1
            push_cast
            ring
          _ <= _ := hsum
      simpa [chenTenReducedArcWeight] using add_le_add_right htail 1
    _ = 5 * (Q : Real) ^ (1 / 5 : Real) - 4 := by
      rw [hcast]
      rw [integral_rpow (r := (-4 / 5 : Real)) (Or.inl (by norm_num))]
      norm_num
      ring
    _ <= 5 * (Q : Real) ^ (1 / 5 : Real) := by linarith

private theorem sum_chenTenArcDenominatorFiber_weight_le (P q : Nat) :
    (∑ i ∈ chenTenArcDenominatorFiber P q,
        chenTenArcWeight i.denominator) <=
      chenTenReducedArcWeight q := by
  let fiber := chenTenArcDenominatorFiber P q
  have hcardNat : fiber.card ≤ q :=
    (card_chenTenArcDenominatorFiber_le_totient P q).trans (Nat.totient_le q)
  have hcardReal : (fiber.card : Real) ≤ q := by exact_mod_cast hcardNat
  calc
    (∑ i ∈ chenTenArcDenominatorFiber P q,
        chenTenArcWeight i.denominator) =
        ∑ _i ∈ fiber, chenTenArcWeight q := by
      apply Finset.sum_congr
      · rfl
      · intro i hi
        have hiq : i.denominator = q := (Finset.mem_filter.mp hi).2
        rw [hiq]
    _ = (fiber.card : Real) * chenTenArcWeight q := by simp
    _ <= (q : Real) * chenTenArcWeight q := by
      exact mul_le_mul_of_nonneg_right hcardReal
        (Real.rpow_nonneg (Nat.cast_nonneg q) _)
    _ = chenTenReducedArcWeight q := by
      by_cases hq0 : q = 0
      · subst q
        norm_num [chenTenArcWeight, chenTenReducedArcWeight]
      · have hqpos : (0 : Real) < q := by
          exact_mod_cast Nat.pos_of_ne_zero hq0
        unfold chenTenArcWeight chenTenReducedArcWeight
        calc
          (q : Real) * (q : Real) ^ (-9 / 5 : Real) =
              (q : Real) ^ (1 : Real) *
                (q : Real) ^ (-9 / 5 : Real) := by rw [Real.rpow_one]
          _ = (q : Real) ^ ((1 : Real) + (-9 / 5 : Real)) := by
            rw [Real.rpow_add hqpos]
          _ = (q : Real) ^ (-4 / 5 : Real) := by norm_num

private theorem sum_chenTenArcWeight_eq_sum_fibers (P : Nat) :
    (∑ i : ChenTenArcIndex P, chenTenArcWeight i.denominator) =
      ∑ q ∈ Finset.range (Nat.sqrt P + 1),
        ∑ i ∈ (Finset.univ : Finset (ChenTenArcIndex P)) with i.denominator = q,
          chenTenArcWeight i.denominator := by
  have hmap : ∀ i ∈ (Finset.univ : Finset (ChenTenArcIndex P)),
      i.denominator ∈ Finset.range (Nat.sqrt P + 1) := by
    intro i hi
    rw [Finset.mem_range]
    have hqS : i.denominator ≤ Nat.sqrt P := by
      rw [Nat.le_sqrt]
      simpa [pow_two] using i.denominator_sq_le
    omega
  symm
  exact Finset.sum_fiberwise_of_maps_to hmap
    (fun i : ChenTenArcIndex P => chenTenArcWeight i.denominator)

private theorem sum_chenTenArcWeight_le_sum_reduced (P : Nat) :
    (∑ i : ChenTenArcIndex P, chenTenArcWeight i.denominator) <=
      ∑ q ∈ Finset.range (Nat.sqrt P + 1), chenTenReducedArcWeight q := by
  rw [sum_chenTenArcWeight_eq_sum_fibers]
  apply Finset.sum_le_sum
  intro q hq
  change (∑ i ∈ chenTenArcDenominatorFiber P q,
      chenTenArcWeight i.denominator) <= chenTenReducedArcWeight q
  exact sum_chenTenArcDenominatorFiber_weight_le P q

/-- The total denominator weight over all reduced arcs is at most
`5 * floor(sqrt P)^(1/5)`. -/
theorem sum_chenTenArcWeight_le_natSqrt (P : Nat) (hP : 1 ≤ P) :
    (∑ i : ChenTenArcIndex P, chenTenArcWeight i.denominator) <=
      5 * (Nat.sqrt P : Real) ^ (1 / 5 : Real) := by
  have hS : 1 ≤ Nat.sqrt P := by
    rw [Nat.le_sqrt]
    simpa using hP
  calc
    (∑ i : ChenTenArcIndex P, chenTenArcWeight i.denominator) <=
        ∑ q ∈ Finset.range (Nat.sqrt P + 1), chenTenReducedArcWeight q :=
      sum_chenTenArcWeight_le_sum_reduced P
    _ = ∑ k ∈ Finset.range (Nat.sqrt P),
        chenTenReducedArcWeight (k + 1) := by
      rw [Finset.sum_range_succ']
      simp [chenTenReducedArcWeight]
    _ <= 5 * (Nat.sqrt P : Real) ^ (1 / 5 : Real) :=
      sum_range_chenTenReducedArcWeight_le (Nat.sqrt P) hS

/-- The fifth root of the natural square root is bounded by the real tenth
root of the original natural number. -/
theorem natSqrt_rpow_one_fifth_le (P : Nat) :
    (Nat.sqrt P : Real) ^ (1 / 5 : Real) <=
      (P : Real) ^ (1 / 10 : Real) := by
  have hsqNat : Nat.sqrt P ^ 2 <= P := by
    simpa [pow_two] using Nat.sqrt_le P
  have hsq : (Nat.sqrt P : Real) ^ (2 : Real) <= (P : Real) := by
    calc
      (Nat.sqrt P : Real) ^ (2 : Real) = (Nat.sqrt P : Real) ^ (2 : Nat) :=
        Real.rpow_ofNat _ 2
      _ <= (P : Real) := by exact_mod_cast hsqNat
  calc
    (Nat.sqrt P : Real) ^ (1 / 5 : Real) =
        (Nat.sqrt P : Real) ^ ((2 : Real) * (1 / 10 : Real)) := by
      norm_num
    _ = ((Nat.sqrt P : Real) ^ (2 : Real)) ^ (1 / 10 : Real) := by
      rw [Real.rpow_mul (by positivity)]
    _ <= (P : Real) ^ (1 / 10 : Real) := by
      exact Real.rpow_le_rpow (by positivity) hsq (by norm_num)

end

end Waring.Analytic
