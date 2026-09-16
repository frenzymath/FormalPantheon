import PrimesRestrictedDigits.ExceptionalMinorArcs.LineSpacing
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A low-height integral relation from many collinear points

This is the source-facing constant-explicit consequence of the finite spacing repair for Lemma
15.1 of `MAYNARD-PRD-PUBLISHED`, pp. 209--210. Its eventual decimal-scale specialization is
used by Proposition 13.4.
-/

namespace PrimesRestrictedDigits

open Filter

private theorem lowHeightBounds_from_spacing
    {X : Nat} (a1 a2 : Fin X) (S : Finset (Fin 3 -> Int))
    (c delta N K : Real)
    (hc : 0 < c) (hdelta : 0 < delta) (hN : 0 < N) (hK : 0 < K)
    (hcount : c * delta * N ^ 2 * K <= (S.card : Real))
    (hscale : 2 <= c * delta * N ^ 2 * K)
    (hwidth : N <= delta * (X : Real))
    (hspacing :
      ∃ v : Fin 3 -> Int,
        v ≠ 0 ∧
        ‖intVectorToEuclidean v‖ *
            ((S.card - 1 : Nat) : Real) <= 2 * N ∧
        |((intVectorDot v (lineCoefficientVector a1 a2) : Int) : Real)| *
            ((S.card - 1 : Nat) : Real) <= 2 * (delta * (X : Real))) :
    ∃ (v : Fin 3 -> Int) (v4 : Int),
      v ≠ 0 ∧
      intVectorDot v (lineCoefficientVector a1 a2) + v4 = 0 ∧
      (∀ i,
        |((v i : Int) : Real)| <=
          (4 / c) * (X : Real) / (N ^ 2 * K)) ∧
      |((v4 : Int) : Real)| <=
        (4 / c) * (X : Real) / (N ^ 2 * K) := by
  let Q : Real := c * delta * N ^ 2 * K
  let D : Real := c * N ^ 2 * K
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hcard : 2 <= S.card := by
    have hcardReal : (2 : Real) <= (S.card : Real) :=
      hscale.trans hcount
    exact_mod_cast hcardReal
  have hcardCast :
      ((S.card - 1 : Nat) : Real) = (S.card : Real) - 1 := by
    rw [Nat.cast_sub (by omega : 1 <= S.card)]
    norm_num
  have hhalf : Q / 2 <= ((S.card - 1 : Nat) : Real) := by
    rw [hcardCast]
    dsimp [Q]
    nlinarith
  obtain ⟨v, hv, hvnorm, hvdot⟩ := hspacing
  have hvnormQ : ‖intVectorToEuclidean v‖ * Q <= 4 * N := by
    have hmul := mul_le_mul_of_nonneg_left hhalf
      (norm_nonneg (intVectorToEuclidean v))
    nlinarith
  have hvnormDdelta :
      (‖intVectorToEuclidean v‖ * D) * delta <=
        (4 * (X : Real)) * delta := by
    calc
      (‖intVectorToEuclidean v‖ * D) * delta =
          ‖intVectorToEuclidean v‖ * Q := by
            dsimp [D, Q]
            ring
      _ <= 4 * N := hvnormQ
      _ <= (4 * (X : Real)) * delta := by nlinarith
  have hvnormD :
      ‖intVectorToEuclidean v‖ * D <= 4 * (X : Real) := by
    exact (mul_le_mul_iff_right₀ hdelta).mp (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hvnormDdelta)
  have hvnormBound :
      ‖intVectorToEuclidean v‖ <=
        (4 / c) * (X : Real) / (N ^ 2 * K) := by
    have hdiv : ‖intVectorToEuclidean v‖ <= 4 * (X : Real) / D :=
      (le_div_iff₀ hD).2 hvnormD
    calc
      ‖intVectorToEuclidean v‖ <= 4 * (X : Real) / D := hdiv
      _ = (4 / c) * (X : Real) / (N ^ 2 * K) := by
        dsimp [D]
        field_simp [hc.ne', hN.ne', hK.ne']

  have hvdotQ :
      |((intVectorDot v (lineCoefficientVector a1 a2) : Int) : Real)| *
          Q <= 4 * (delta * (X : Real)) := by
    have hmul := mul_le_mul_of_nonneg_left hhalf
      (abs_nonneg
        (((intVectorDot v (lineCoefficientVector a1 a2) : Int) : Real)))
    nlinarith
  have hvdotDdelta :
      (|((intVectorDot v (lineCoefficientVector a1 a2) : Int) : Real)| *
          D) * delta <= (4 * (X : Real)) * delta := by
    calc
      (|((intVectorDot v (lineCoefficientVector a1 a2) : Int) : Real)| *
          D) * delta =
          |((intVectorDot v (lineCoefficientVector a1 a2) : Int) : Real)| *
            Q := by
              dsimp [D, Q]
              ring
      _ <= 4 * (delta * (X : Real)) := hvdotQ
      _ = (4 * (X : Real)) * delta := by ring
  have hvdotD :
      |((intVectorDot v (lineCoefficientVector a1 a2) : Int) : Real)| *
          D <= 4 * (X : Real) := by
    exact (mul_le_mul_iff_right₀ hdelta).mp (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hvdotDdelta)
  have hvdotBound :
      |((intVectorDot v (lineCoefficientVector a1 a2) : Int) : Real)| <=
        (4 / c) * (X : Real) / (N ^ 2 * K) := by
    have hdiv :
        |((intVectorDot v (lineCoefficientVector a1 a2) : Int) : Real)| <=
          4 * (X : Real) / D :=
      (le_div_iff₀ hD).2 hvdotD
    calc
      |((intVectorDot v (lineCoefficientVector a1 a2) : Int) : Real)| <=
          4 * (X : Real) / D := hdiv
      _ = (4 / c) * (X : Real) / (N ^ 2 * K) := by
        dsimp [D]
        field_simp [hc.ne', hN.ne', hK.ne']

  refine ⟨v, -intVectorDot v (lineCoefficientVector a1 a2),
    hv, by simp, ?_, ?_⟩
  · intro i
    have hi := PiLp.norm_apply_le (intVectorToEuclidean v) i
    simpa [Real.norm_eq_abs] using hi.trans hvnormBound
  · simpa using hvdotBound

/--
Many bounded integer points on one line give a nontrivial exact integral
relation whose four coefficients have the source-required height.
-/
theorem exists_lowHeightIntegerRelation_of_collinear
    {X : Nat} (hX : 0 < X) (a1 a2 : Fin X)
    (line : Submodule Real (EuclideanSpace Real (Fin 3)))
    (hline : Module.finrank Real line = 1)
    (S : Finset (Fin 3 -> Int)) (c delta N K : Real)
    (hc : 0 < c) (hdelta : 0 < delta) (hN : 0 < N) (hK : 0 < K)
    (hcount : c * delta * N ^ 2 * K <= (S.card : Real))
    (hscale : 2 <= c * delta * N ^ 2 * K)
    (hwidth : N <= delta * (X : Real))
    (hmem : ∀ z ∈ S, intVectorToEuclidean z ∈ line)
    (hnorm : ∀ z ∈ S, ‖intVectorToEuclidean z‖ <= N)
    (hdot : ∀ z ∈ S,
      |((intVectorDot z (lineCoefficientVector a1 a2) : Int) : Real)| <=
        delta * (X : Real)) :
    ∃ (v : Fin 3 -> Int) (v4 : Int),
      v ≠ 0 ∧
      intVectorDot v (lineCoefficientVector a1 a2) + v4 = 0 ∧
      (∀ i,
        |((v i : Int) : Real)| <=
          (4 / c) * (X : Real) / (N ^ 2 * K)) ∧
      |((v4 : Int) : Real)| <=
        (4 / c) * (X : Real) / (N ^ 2 * K) := by
  have hXReal : (0 : Real) < X := by exact_mod_cast hX
  have hcard : 2 <= S.card := by
    have hcardReal : (2 : Real) <= (S.card : Real) :=
      hscale.trans hcount
    exact_mod_cast hcardReal
  apply lowHeightBounds_from_spacing a1 a2 S c delta N K
    hc hdelta hN hK hcount hscale hwidth
  exact exists_collinear_intVector_spacing line hline
    (lineCoefficientVector a1 a2) S N (delta * (X : Real))
    hN.le (mul_nonneg hdelta.le hXReal.le) hcard
    hmem hnorm hdot

/--
At the decimal scales of Proposition 13.4, the line-count coefficient is at
least two beyond one threshold chosen uniformly before `N`, `K`, and
`delta`.
-/
theorem eventually_two_le_lineCountScale :
    ∃ length0 : Nat, ∀ length : Nat, length0 <= length ->
      ∀ N K delta : Real,
        (((10 ^ length : Nat) : Real) ^ (9 / 25 : Real) <= N) ->
        1 <= K ->
        N <= delta * ((10 ^ length : Nat) : Real) ->
        2 <= delta * N ^ 2 * K := by
  have hXpow :
      Tendsto (fun length : Nat => ((10 ^ length : Nat) : Real))
        atTop atTop := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (tendsto_pow_atTop_atTop_of_one_lt
        (by norm_num : (1 : Real) < 10))
  have hgrowth :
      Tendsto
        (fun length : Nat =>
          (((10 ^ length : Nat) : Real) ^ (2 / 25 : Real)))
        atTop atTop :=
    (tendsto_rpow_atTop
      (by norm_num : (0 : Real) < 2 / 25)).comp hXpow
  apply eventually_atTop.mp
  filter_upwards [hgrowth.eventually_ge_atTop (2 : Real)] with
      length hlength
  intro N K delta hNlower hK hwidth
  let X : Real := ((10 ^ length : Nat) : Real)
  have hX : 0 < X := by
    dsimp [X]
    positivity
  have hNpos : 0 < N :=
    (Real.rpow_pos_of_pos hX (9 / 25 : Real)).trans_le hNlower
  have hNcube : (X ^ (9 / 25 : Real)) ^ 3 <= N ^ 3 :=
    pow_le_pow_left₀ (Real.rpow_nonneg hX.le _) hNlower 3
  have hpowerIdentity :
      X ^ (2 / 25 : Real) =
        (X ^ (9 / 25 : Real)) ^ 3 / X := by
    calc
      X ^ (2 / 25 : Real) =
          X ^ ((9 / 25 : Real) * 3 - 1) := by norm_num
      _ = X ^ ((9 / 25 : Real) * 3) / X ^ (1 : Real) :=
        Real.rpow_sub hX _ _
      _ = (X ^ (9 / 25 : Real)) ^ 3 / X := by
        rw [Real.rpow_mul hX.le, Real.rpow_one]
        exact congrArg (fun y : Real => y / X)
          (Real.rpow_natCast (X ^ (9 / 25 : Real)) 3)
  have hfirst : X ^ (2 / 25 : Real) <= N ^ 3 / X := by
    rw [hpowerIdentity]
    exact (div_le_div_iff_of_pos_right hX).2 hNcube
  have hNdiv : N / X <= delta := by
    apply (div_le_iff₀ hX).2
    simpa [X] using hwidth
  have hdelta : 0 < delta :=
    (div_pos hNpos hX).trans_le hNdiv
  have hsecond : N ^ 3 / X <= delta * N ^ 2 * K := by
    calc
      N ^ 3 / X = (N / X) * N ^ 2 := by ring
      _ <= delta * N ^ 2 :=
        mul_le_mul_of_nonneg_right hNdiv (sq_nonneg N)
      _ = (delta * N ^ 2) * 1 := by ring
      _ <= (delta * N ^ 2) * K :=
        mul_le_mul_of_nonneg_left hK
          (mul_nonneg hdelta.le (sq_nonneg N))
      _ = delta * N ^ 2 * K := rfl
  exact hlength.trans (hfirst.trans hsecond)

end PrimesRestrictedDigits
