import PrimesRestrictedDigits.ExceptionalMinorArcs.DirichletBands
import PrimesRestrictedDigits.LatticeEstimates.RationalApproximationBands

/-!
# Canonical scales for the Dirichlet rational bands

This assigns the approximation from `DirichletBands` to one denominator scale and one
signed-error scale. The exact-error fiber is indexed by zero; positive indices encode the
decimal exponent after shifting by `X^2`.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Decimal index of the canonical denominator scale before the terminal
square-root cap is applied. -/
noncomputable def exceptionalDirichletDenominatorIndex
    (X : Nat) (a : Fin X) : Nat :=
  factorTenIndex (exceptionalDirichletApproximation X a).den

/-- Zero indexes exact approximation; a positive index stores one more than
the shifted error's decimal exponent. -/
noncomputable def exceptionalDirichletErrorIndex
    (X : Nat) (a : Fin X) : Nat :=
  if exceptionalDirichletError X a = 0 then 0
  else latticePositiveRealFactorTenExponent
    (exceptionalDirichletErrorTarget X a) + 1

/-- Denominator scale represented by a finite cover index. -/
noncomputable def exceptionalDirichletDenominatorScaleAt
    (X i : Nat) : Real :=
  min (((10 ^ i : Nat) : Real)) (Real.sqrt (X : Real))

/-- Error scale represented by a finite cover index. -/
noncomputable def exceptionalDirichletErrorScaleAt
    (X j : Nat) : Real :=
  match j with
  | 0 => 0
  | j + 1 => ((10 ^ j : Nat) : Real) / (X : Real)

@[simp]
theorem exceptionalDirichletDenominatorScaleAt_index
    (X : Nat) (a : Fin X) :
    exceptionalDirichletDenominatorScaleAt X
        (exceptionalDirichletDenominatorIndex X a) =
      exceptionalDirichletDenominatorScale X a := by
  rfl

@[simp]
theorem exceptionalDirichletErrorScaleAt_index
    (X : Nat) (a : Fin X) :
    exceptionalDirichletErrorScaleAt X
        (exceptionalDirichletErrorIndex X a) =
      exceptionalDirichletErrorScale X a := by
  by_cases herror : exceptionalDirichletError X a = 0
  · simp [exceptionalDirichletErrorIndex,
      exceptionalDirichletErrorScale, herror,
      exceptionalDirichletErrorScaleAt]
  · simp [exceptionalDirichletErrorIndex,
      exceptionalDirichletErrorScale, herror,
      exceptionalDirichletErrorScaleAt,
      latticePositiveRealFactorTenScale]

/-- The canonical signed error lies in its repaired exact factor-ten band. -/
theorem exceptionalDirichletErrorScale_in_band
    {X : Nat} (hX : 4 <= X) (a : Fin X) :
    latticeRationalErrorInBand (X : Real)
      (exceptionalDirichletErrorScale X a)
      (exceptionalDirichletError X a) := by
  by_cases herror : exceptionalDirichletError X a = 0
  · exact Or.inl <| by simp [exceptionalDirichletErrorScale, herror]
  · right
    have hXPos : (0 : Real) < X := by positivity
    have htarget := exceptionalDirichletErrorTarget_gt_one hX a herror
    have hscale := latticePositiveRealFactorTenScale_bounds htarget
    have hscalePos : (0 : Real) <
        latticePositiveRealFactorTenScale
          (exceptionalDirichletErrorTarget X a) := by
      unfold latticePositiveRealFactorTenScale
      positivity
    unfold exceptionalDirichletErrorScale
    rw [if_neg herror]
    refine ⟨div_pos hscalePos hXPos, ?_, ?_⟩
    · unfold exceptionalDirichletErrorTarget at hscale ⊢
      have h := hscale.2
      apply (div_lt_iff₀ (by norm_num : (0 : Real) < 10)).2
      apply (div_lt_iff₀ hXPos).2
      apply (div_lt_iff₀ hXPos).2
      nlinarith [h]
    · unfold exceptionalDirichletErrorTarget at hscale ⊢
      have h := hscale.1
      apply (le_div_iff₀ hXPos).2
      apply (le_div_iff₀ hXPos).2
      nlinarith [h]

/-- Quantitative hypotheses for the repaired rational band. The final
alternative records that a nonzero error scale is genuinely larger than the
smallest source scale `1 / X`. -/
theorem exceptionalDirichletScales_bounds
    {X : Nat} (hX : 4 <= X) (a : Fin X) :
    1 <= exceptionalDirichletDenominatorScale X a ∧
      exceptionalDirichletDenominatorScale X a <=
        Real.sqrt (X : Real) ∧
      0 <= exceptionalDirichletErrorScale X a ∧
      exceptionalDirichletErrorScale X a <
        100 * Real.sqrt (X : Real) /
          exceptionalDirichletDenominatorScale X a ∧
      (exceptionalDirichletErrorScale X a = 0 ∨
        1 / (X : Real) < exceptionalDirichletErrorScale X a) := by
  let x : Real := X
  let q : Real := (exceptionalDirichletApproximation X a).den
  let Q : Real := exceptionalDirichletDenominatorScale X a
  let nu : Real := exceptionalDirichletError X a
  have hx : 0 < x := by dsimp [x]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hQdata := exceptionalDirichletDenominatorScale_bounds
    (show 1 <= X by omega) a
  have hqQ : q <= Q := by simpa only [q, Q] using hQdata.1
  have hQlt : Q < 10 * q := by simpa only [q, Q] using hQdata.2.1
  have hQsqrt : Q <= Real.sqrt x := by
    simpa only [x, Q] using hQdata.2.2
  have hqOne : (1 : Real) <= q := by
    dsimp only [q]
    exact_mod_cast (exceptionalDirichletApproximation X a).den_pos
  have hQOne : (1 : Real) <= Q := hqOne.trans hqQ
  have hQPos : 0 < Q := Real.zero_lt_one.trans_le hQOne
  refine ⟨by simpa only [Q] using hQOne,
    by simpa only [x, Q] using hQsqrt, ?_⟩
  by_cases herror : exceptionalDirichletError X a = 0
  · have hscaleZero : exceptionalDirichletErrorScale X a = 0 := by
      simp [exceptionalDirichletErrorScale, herror]
    rw [hscaleZero]
    refine ⟨le_rfl, ?_, Or.inl rfl⟩
    positivity
  · have htarget := exceptionalDirichletErrorTarget_gt_one hX a herror
    have hdecimal := latticePositiveRealFactorTenScale_bounds htarget
    have hdirichlet := exceptionalDirichletApproximation_error_le
      (show 1 <= X by omega) a
    have hsquare : Real.sqrt x * Real.sqrt x = x :=
      Real.mul_self_sqrt hx.le
    have hupper : exceptionalDirichletErrorScale X a <
        100 * Real.sqrt x / Q := by
      unfold exceptionalDirichletErrorScale
      rw [if_neg herror]
      calc
        (latticePositiveRealFactorTenScale
              (exceptionalDirichletErrorTarget X a) : Real) /
            (X : Real) <
            (10 * exceptionalDirichletErrorTarget X a) / x := by
          simpa only [x] using
            div_lt_div_of_pos_right hdecimal.2 hx
        _ = 10 * x * abs nu := by
          unfold exceptionalDirichletErrorTarget
          dsimp only [x, nu]
          field_simp
        _ <= 10 * x * (1 / (Real.sqrt x * q)) := by
          gcongr
        _ = 10 * Real.sqrt x / q := by
          field_simp
          nlinarith [hsquare]
        _ < 100 * Real.sqrt x / Q := by
          rw [div_lt_div_iff₀ hq hQPos]
          nlinarith
    have hdecimalOne : (1 : Real) <
        latticePositiveRealFactorTenScale
          (exceptionalDirichletErrorTarget X a) :=
      htarget.trans_le hdecimal.1
    have hlower : 1 / (X : Real) <
        exceptionalDirichletErrorScale X a := by
      unfold exceptionalDirichletErrorScale
      rw [if_neg herror]
      exact (div_lt_div_iff_of_pos_right
        (by simpa only [x] using hx)).2 hdecimalOne
    refine ⟨(show (0 : Real) <= 1 / (X : Real) by positivity).trans
        hlower.le, ?_, Or.inr hlower⟩
    simpa only [x, Q] using hupper

/-- The canonical approximation belongs to the rational band selected by its
two canonical scales. -/
theorem mem_latticeRationalApproximationBand_canonical
    {X : Nat} (hX : 4 <= X) (a : Fin X) :
    a ∈ latticeRationalApproximationBand
      (exceptionalDirichletDenominatorScale X a)
      (exceptionalDirichletErrorScale X a) := by
  classical
  rw [latticeRationalApproximationBand, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  refine ⟨exceptionalDirichletApproximation X a, ?_, ?_, ?_⟩
  · exact (exceptionalDirichletDenominatorScale_bounds
      (show 1 <= X by omega) a).1
  · exact (exceptionalDirichletDenominatorScale_bounds
      (show 1 <= X by omega) a).2.1
  · simpa only [exceptionalDirichletError] using
      exceptionalDirichletErrorScale_in_band hX a

end

end PrimesRestrictedDigits
