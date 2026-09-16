import PrimesRestrictedDigits.MajorArcs.Subdivision
import Mathlib.Data.Nat.ModEq
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Major-arc phase linearization

This supplies the pointwise phase error and the corrected roots-of-unity
cancellation from the major-arc argument on published pp. 187--188.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The analytic-number-theory phase `e(t) = exp(2 * pi * i * t)`. -/
noncomputable def majorArcPhase (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

private theorem majorArcPhase_add (x y : ℝ) :
    majorArcPhase (x + y) = majorArcPhase x * majorArcPhase y := by
  rw [majorArcPhase, majorArcPhase, majorArcPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem norm_majorArcPhase (x : ℝ) : ‖majorArcPhase x‖ = 1 := by
  rw [majorArcPhase]
  exact Complex.norm_exp_ofReal_mul_I _

private theorem norm_majorArcPhase_sub_le (x y : ℝ) :
    ‖majorArcPhase x - majorArcPhase y‖ ≤ 2 * Real.pi * |x - y| := by
  have hfactor : majorArcPhase x - majorArcPhase y =
      majorArcPhase y * (majorArcPhase (x - y) - 1) := by
    rw [mul_sub, mul_one, ← majorArcPhase_add]
    congr 2
    ring
  rw [hfactor, norm_mul, norm_majorArcPhase, one_mul]
  have hexp : majorArcPhase (x - y) =
      Complex.exp (Complex.I * (2 * Real.pi * (x - y) : ℝ)) := by
    rw [majorArcPhase]
    congr 1
    push_cast
    ring
  rw [hexp]
  calc
    ‖Complex.exp (Complex.I * (2 * Real.pi * (x - y) : ℝ)) - 1‖ ≤
        ‖(2 * Real.pi * (x - y) : ℝ)‖ :=
      Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * Real.pi * |x - y| := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by norm_num),
        abs_of_pos Real.pi_pos]

private theorem majorArcPhase_add_int (x : ℝ) (n : ℤ) :
    majorArcPhase (x + n) = majorArcPhase x := by
  rw [majorArcPhase, majorArcPhase]
  have harg : (((2 * Real.pi * (x + n) : ℝ) : ℂ) * Complex.I) =
      (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) +
        (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Signed rational phases agree on congruent natural arguments. -/
theorem majorArcPhase_int_of_modEq
    {n r q : ℕ} (hq : 0 < q) (b : ℤ) (hmod : n ≡ r [MOD q]) :
    majorArcPhase ((n : ℝ) * (b : ℝ) / (q : ℝ)) =
      majorArcPhase ((b : ℝ) * (r : ℝ) / (q : ℝ)) := by
  rcases Nat.modEq_iff_dvd.mp hmod with ⟨z, hz⟩
  have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hzReal : (r : ℝ) - (n : ℝ) = (q : ℝ) * (z : ℝ) := by
    exact_mod_cast hz
  have hshift : (n : ℝ) * (b : ℝ) / (q : ℝ) =
      (b : ℝ) * (r : ℝ) / (q : ℝ) + (((-b * z : ℤ)) : ℝ) := by
    push_cast
    field_simp
    rw [show (n : ℝ) = r - q * z by linarith [hzReal]]
    ring
  rw [hshift, majorArcPhase_add_int]

theorem majorArcPhase_of_modEq
    {m p r q b : ℕ} (hq : 0 < q) (hmod : p ≡ r [MOD q]) :
    majorArcPhase (((m * p * b : ℕ) : ℝ) / (q : ℝ)) =
      majorArcPhase (((b * r * m : ℕ) : ℝ) / (q : ℝ)) := by
  rcases (Nat.modEq_iff_dvd.mp hmod) with ⟨z, hz⟩
  have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hzReal : (r : ℝ) - (p : ℝ) = (q : ℝ) * (z : ℝ) := by exact_mod_cast hz
  have hshift : (((m * p * b : ℕ) : ℝ) / (q : ℝ)) =
      (((b * r * m : ℕ) : ℝ) / (q : ℝ)) +
        (((-(m : ℤ) * (b : ℤ) * z : ℤ)) : ℝ) := by
    push_cast
    field_simp
    rw [show (p : ℝ) = r - q * z by linarith [hzReal]]
    ring
  rw [hshift, majorArcPhase_add_int]

/-- The signed-numerator phase is constant on a residue class up to the
linearization error contributed by one subdivision block. -/
theorem majorArcBlock_phase_error_le_int
    {X : ℝ} {J m j p residue q : ℕ} {b c : ℤ}
    (hX : 0 < X) (hJ : 0 < J) (hm : 0 < m)
    (hp : p ∈ majorArcBlock X J m j)
    (hq : 0 < q) (hmod : p ≡ residue [MOD q]) :
    ‖majorArcPhase (((m * p : ℕ) : ℝ) *
          ((b : ℝ) / (q : ℝ) + (c : ℝ) / X)) -
        majorArcPhase
            ((b : ℝ) * (residue : ℝ) * (m : ℝ) / (q : ℝ)) *
          majorArcPhase
            ((j : ℝ) * majorArcSubdivisionWidth J * (c : ℝ))‖ ≤
      2 * Real.pi * |(c : ℝ)| * majorArcSubdivisionWidth J := by
  let A := (b : ℝ) * (residue : ℝ) * (m : ℝ) / (q : ℝ)
  let u := (c : ℝ) * (((m * p : ℕ) : ℝ) / X)
  let v := (c : ℝ) * ((j : ℝ) / (J : ℝ))
  have hmpmod : m * p ≡ m * residue [MOD q] := hmod.mul_left m
  have hactual : majorArcPhase (((m * p : ℕ) : ℝ) *
      ((b : ℝ) / (q : ℝ) + (c : ℝ) / X)) = majorArcPhase (A + u) := by
    rw [show (((m * p : ℕ) : ℝ) *
        ((b : ℝ) / (q : ℝ) + (c : ℝ) / X)) =
          (((m * p : ℕ) : ℝ) * (b : ℝ) / (q : ℝ)) + u by
        dsimp [u]
        ring]
    rw [majorArcPhase_add]
    have hphase := majorArcPhase_int_of_modEq hq b hmpmod
    rw [hphase, ← majorArcPhase_add]
    congr 1
    dsimp [A]
    push_cast
    ring
  have hexpected : majorArcPhase
      ((b : ℝ) * (residue : ℝ) * (m : ℝ) / (q : ℝ)) *
        majorArcPhase
          ((j : ℝ) * majorArcSubdivisionWidth J * (c : ℝ)) =
      majorArcPhase (A + v) := by
    rw [← majorArcPhase_add]
    congr 1
    dsimp [A, v]
    rw [majorArcSubdivisionWidth, inv_eq_one_div]
    ring
  rw [hactual, hexpected]
  have hscaled := majorArcBlock_scaled_sub_left hX hJ hm hp
  calc
    ‖majorArcPhase (A + u) - majorArcPhase (A + v)‖ ≤
        2 * Real.pi * |(A + u) - (A + v)| := norm_majorArcPhase_sub_le _ _
    _ = 2 * Real.pi * (|(c : ℝ)| *
        |((m * p : ℕ) : ℝ) / X - (j : ℝ) / (J : ℝ)|) := by
      dsimp [u, v]
      rw [show A + (c : ℝ) * (((m * p : ℕ) : ℝ) / X) -
          (A + (c : ℝ) * ((j : ℝ) / (J : ℝ))) =
          (c : ℝ) * ((((m * p : ℕ) : ℝ) / X) -
            (j : ℝ) / (J : ℝ)) by ring, abs_mul]
    _ ≤ 2 * Real.pi * |(c : ℝ)| * majorArcSubdivisionWidth J := by
      have herr : |((m * p : ℕ) : ℝ) / X - (j : ℝ) / (J : ℝ)| ≤
          majorArcSubdivisionWidth J := by
        rw [abs_of_nonneg hscaled.1]
        exact hscaled.2.le
      calc
        2 * Real.pi * (|(c : ℝ)| *
            |((m * p : ℕ) : ℝ) / X - (j : ℝ) / (J : ℝ)|) ≤
            2 * Real.pi * (|(c : ℝ)| * majorArcSubdivisionWidth J) := by
          gcongr
        _ = _ := by ring

theorem majorArcBlock_phase_error_le
    {X : ℝ} {J m j p r q b : ℕ} {c : ℤ}
    (hX : 0 < X) (hJ : 0 < J) (hm : 0 < m)
    (hp : p ∈ majorArcBlock X J m j)
    (hq : 0 < q) (hmod : p ≡ r [MOD q]) :
    ‖majorArcPhase (((m * p : ℕ) : ℝ) *
          ((b : ℝ) / (q : ℝ) + (c : ℝ) / X)) -
        majorArcPhase (((b * r * m : ℕ) : ℝ) / (q : ℝ)) *
          majorArcPhase
            ((j : ℝ) * majorArcSubdivisionWidth J * (c : ℝ))‖ ≤
      2 * Real.pi * |(c : ℝ)| * majorArcSubdivisionWidth J := by
  simpa only [Int.cast_natCast, Nat.cast_mul] using
    (majorArcBlock_phase_error_le_int (b := (b : ℤ)) hX hJ hm hp hq hmod)

private theorem majorArcPhase_eq_one_iff_dvd
    {J : ℕ} (hJ : J ≠ 0) (c : ℤ) :
    majorArcPhase ((c : ℝ) / (J : ℝ)) = 1 ↔ (J : ℤ) ∣ c := by
  rw [majorArcPhase, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    have hfactor : ((((c : ℝ) / (J : ℝ) : ℝ) : ℂ) *
        (2 * (Real.pi : ℂ) * Complex.I)) =
        (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      calc
        ((((c : ℝ) / (J : ℝ) : ℝ) : ℂ) *
            (2 * (Real.pi : ℂ) * Complex.I)) =
            (((2 * Real.pi * ((c : ℝ) / (J : ℝ)) : ℝ) : ℂ) *
              Complex.I) := by push_cast; ring
        _ = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := hn
    have hratioComplex : ((((c : ℝ) / (J : ℝ) : ℝ) : ℂ)) = (n : ℂ) :=
      mul_right_cancel₀ Complex.two_pi_I_ne_zero hfactor
    have hratio : (c : ℝ) / (J : ℝ) = (n : ℝ) :=
      Complex.ofReal_injective hratioComplex
    have hcast : (c : ℝ) = (J : ℝ) * (n : ℝ) := by
      have hJreal : (J : ℝ) ≠ 0 := by exact_mod_cast hJ
      rw [← hratio]
      field_simp
    exact ⟨n, by exact_mod_cast hcast⟩
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    have hJreal : (J : ℝ) ≠ 0 := by exact_mod_cast hJ
    push_cast
    field_simp

private theorem majorArcPhase_mul_nat (x : ℝ) (j : ℕ) :
    majorArcPhase ((j : ℝ) * x) = majorArcPhase x ^ j := by
  rw [majorArcPhase, majorArcPhase, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem majorArcPhase_pow_count
    {J : ℕ} (hJ : J ≠ 0) (c : ℤ) :
    majorArcPhase ((c : ℝ) / (J : ℝ)) ^ J = 1 := by
  rw [← majorArcPhase_mul_nat]
  have hJreal : (J : ℝ) ≠ 0 := by exact_mod_cast hJ
  rw [show (J : ℝ) * ((c : ℝ) / (J : ℝ)) = (c : ℝ) by field_simp]
  change Complex.exp (((2 * Real.pi * (c : ℝ) : ℝ) : ℂ) * Complex.I) = 1
  have harg : (((2 * Real.pi * (c : ℝ) : ℝ) : ℂ) * Complex.I) =
      (c : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [harg, Complex.exp_int_mul_two_pi_mul_I]

theorem majorArcPhase_sum_Ico_one_eq_neg_one
    {J : ℕ} (hJ : 1 < J) {c : ℤ} (hnotdvd : ¬(J : ℤ) ∣ c) :
    (∑ j ∈ Finset.Ico 1 J,
      majorArcPhase ((j : ℝ) * (c : ℝ) / J)) = -1 := by
  let z := majorArcPhase ((c : ℝ) / (J : ℝ))
  have hJ0 : J ≠ 0 := (Nat.zero_lt_of_lt hJ).ne'
  have hz : z ≠ 1 := by
    change majorArcPhase ((c : ℝ) / (J : ℝ)) ≠ 1
    intro hz1
    exact hnotdvd ((majorArcPhase_eq_one_iff_dvd hJ0 c).mp hz1)
  have hzJ : z ^ J = 1 := by
    change majorArcPhase ((c : ℝ) / (J : ℝ)) ^ J = 1
    exact majorArcPhase_pow_count hJ0 c
  have hterm (j : ℕ) :
      majorArcPhase ((j : ℝ) * (c : ℝ) / (J : ℝ)) = z ^ j := by
    change majorArcPhase ((j : ℝ) * (c : ℝ) / (J : ℝ)) =
      majorArcPhase ((c : ℝ) / (J : ℝ)) ^ j
    rw [← majorArcPhase_mul_nat]
    congr 1
    ring
  simp_rw [hterm]
  rw [geom_sum_Ico hz (Nat.one_le_iff_ne_zero.mpr hJ0), hzJ, pow_one]
  field_simp
  ring

theorem majorArcPhase_sum_Ico_one_eq_neg_one_of_abs_lt
    {J : ℕ} (hJ : 1 < J) {c : ℤ} (hc : c ≠ 0) (hcJ : c.natAbs < J) :
    (∑ j ∈ Finset.Ico 1 J,
      majorArcPhase ((j : ℝ) * (c : ℝ) / J)) = -1 := by
  apply majorArcPhase_sum_Ico_one_eq_neg_one hJ
  intro hdvd
  have hle : J ≤ c.natAbs := by
    simpa using Int.natAbs_le_of_dvd_ne_zero hdvd hc
  exact (not_le_of_gt hcJ) hle

theorem prime_le_modulus_of_not_coprime_modEq
    {p r q : ℕ} (hp : p.Prime) (hq : 0 < q)
    (hmod : p ≡ r [MOD q]) (hrq : ¬Nat.Coprime r q) :
    p ≤ q := by
  let d := Nat.gcd r q
  have hdq : d ∣ q := Nat.gcd_dvd_right r q
  have hdr : d ∣ r := Nat.gcd_dvd_left r q
  have hdmod : p ≡ r [MOD d] := hmod.of_dvd hdq
  have hrzero : r ≡ 0 [MOD d] := hdr.modEq_zero_nat
  have hdp : d ∣ p := Nat.modEq_zero_iff_dvd.mp (hdmod.trans hrzero)
  have hdne : d ≠ 1 := by
    intro hd
    apply hrq
    rw [Nat.coprime_iff_gcd_eq_one]
    exact hd
  have hdpeq : d = p := (hp.eq_one_or_self_of_dvd d hdp).resolve_left hdne
  rw [← hdpeq]
  exact Nat.le_of_dvd hq hdq

end PrimesRestrictedDigits
