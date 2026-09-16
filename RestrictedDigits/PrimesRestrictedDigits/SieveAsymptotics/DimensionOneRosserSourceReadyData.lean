import PrimesRestrictedDigits.SieveAsymptotics.DecimalDensityRatio
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceProfileEndpoint

/-!
# Source cutoff and all-state selection

This selects the literal source cutoff from the local logarithmic level and records its exact
comparison with every current coordinate. The direct branch carries no source target.
-/

namespace PrimesRestrictedDigits

/--
A fresh source cutoff and every cutoff-dependent premise of the joint ledgers. The package is
independent of the current coordinate.
-/
structure DimensionOneRosserSourceCutoffData
    (K S level : Real) where
  /-- The fresh local source cutoff coordinate. -/
  s0 : Real
  /-- The arithmetic cutoff lies in the density-estimate domain. -/
  hcutoff : 2 <= level ^ (1 / s0)
  /-- The cutoff clears the uniform source tail. -/
  hsTail : S <= s0
  /-- Iwaniec's literal Eq. (8.7) source cutoff. -/
  hsource : s0 ^ 50 = Real.log level *
    (Real.log (Real.log level)) ^ 3
  /-- The logarithmic level lies in the positive source domain. -/
  hLExp : Real.exp 1 <= Real.log level
  /-- The explicit source logarithmic slope gate. -/
  hgate : 124800 + 14400 * Real.log (Real.log (Real.log level)) <=
    Real.log (Real.log level)
  /-- The fixed-splice second-level growth threshold. -/
  hgrowth : dimensionOneRosserSecondLevelThreshold <= Real.log level
  /-- The exact small-coefficient reserve. -/
  hsmall : 6 * (1 + 2304 * K) <=
    (Real.log level) ^ (1 / 24 : Real)

/-- The same selected source cutoff together with its exhaustive comparison
to one current coordinate. The strict right branch lies below the cutoff. -/
structure DimensionOneRosserSourceAllStateData
    (K S level s : Real) where
  cutoff : DimensionOneRosserSourceCutoffData K S level
  direct_or_ready : cutoff.s0 <= s \/ s < cutoff.s0

/-- A sufficiently large logarithmic level supplies the canonical literal
source cutoff, uniformly before the current coordinate. -/
theorem exists_dimensionOneRosserSourceCutoffData_threshold
    {K S : Real} (hK : 0 <= K)
    (hS : Real.exp 5000 + 1 <= S) :
    exists Lambda : Real, Real.exp 1 <= Lambda /\
      forall {level : Real}, 2 <= level ->
        Lambda <= Real.log level ->
        Nonempty (DimensionOneRosserSourceCutoffData K S level) := by
  obtain ⟨L0, hL0Exp, hL0gate⟩ :=
    exists_dimensionOneRosserSourceCutoffSlopeGate
  let C : Real := 6 * (1 + 2304 * K)
  let Lambda : Real := max L0
    (max dimensionOneRosserSecondLevelThreshold
      (max (S ^ (50 : Nat)) (C ^ (24 : Nat))))
  have hLambdaExp : Real.exp 1 <= Lambda :=
    hL0Exp.trans (le_max_left _ _)
  refine ⟨Lambda, hLambdaExp, ?_⟩
  intro level hlevel hlarge
  let L : Real := Real.log level
  let A : Real := L * (Real.log L) ^ 3
  let s0 : Real := A ^ (1 / 50 : Real)
  have hL0L : L0 <= L :=
    (le_max_left L0 _).trans hlarge
  have hLExp : Real.exp 1 <= L := hL0Exp.trans hL0L
  have hLPos : 0 < L := (Real.exp_pos 1).trans_le hLExp
  have hlogLOne : 1 <= Real.log L :=
    (Real.le_log_iff_exp_le hLPos).2 hLExp
  have hlogLPos : 0 < Real.log L := zero_lt_one.trans_le hlogLOne
  have hApos : 0 < A := mul_pos hLPos (pow_pos hlogLPos 3)
  have hs0Nonneg : 0 <= s0 := Real.rpow_nonneg hApos.le _
  have hsource : s0 ^ (50 : Nat) = A := by
    dsimp only [s0]
    convert Real.rpow_inv_natCast_pow (n := 50) hApos.le
      (by norm_num : (50 : Nat) ≠ 0) using 1; norm_num
  have hSPow : S ^ (50 : Nat) <= L := by
    exact (le_max_left (S ^ (50 : Nat)) (C ^ (24 : Nat))).trans
      ((le_max_right dimensionOneRosserSecondLevelThreshold
        (max (S ^ (50 : Nat)) (C ^ (24 : Nat)))).trans
        ((le_max_right L0 _).trans hlarge))
  have hLleA : L <= A := by
    dsimp only [A]
    calc
      L = L * 1 := by ring
      _ <= L * (Real.log L) ^ 3 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hlogLOne) hLPos.le
  have hs0S : S <= s0 := by
    have hSNonneg : 0 <= S := by
      linarith [Real.exp_pos (5000 : Real)]
    apply (pow_le_pow_iff_left₀ hSNonneg hs0Nonneg
      (by norm_num : (50 : Nat) ≠ 0)).mp
    rw [hsource]
    exact hSPow.trans hLleA
  have hs0One : 1 <= s0 := by
    have hSOne : 1 <= S := by
      linarith [Real.exp_pos (5000 : Real)]
    exact hSOne.trans hs0S
  have hs0Pos : 0 < s0 := zero_lt_one.trans_le hs0One
  have hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L :=
    hL0gate hL0L
  have hs0L : s0 <= L :=
    dimensionOneRosserSourceCutoff_s0_le_log hs0One hsource hLExp hgate
  have hlevelPos : 0 < level := by linarith
  have hlogCutoff : 1 <= Real.log (level ^ (1 / s0)) := by
    rw [log_rpow_one_div hlevelPos]
    exact (one_le_div hs0Pos).2 hs0L
  have hcutoffPos : 0 < level ^ (1 / s0) :=
    Real.rpow_pos_of_pos hlevelPos _
  have hcutoff : 2 <= level ^ (1 / s0) := by
    apply (Real.log_le_log_iff (by norm_num) hcutoffPos).mp
    have hlogTwo : Real.log 2 <= 1 := by
      convert Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
        using 1; norm_num
    exact hlogTwo.trans hlogCutoff
  have hgrowth : dimensionOneRosserSecondLevelThreshold <= L := by
    exact (le_max_left dimensionOneRosserSecondLevelThreshold
      (max (S ^ (50 : Nat)) (C ^ (24 : Nat)))).trans
        ((le_max_right L0 _).trans hlarge)
  have hCPow : C ^ (24 : Nat) <= L := by
    exact (le_max_right (S ^ (50 : Nat)) (C ^ (24 : Nat))).trans
      ((le_max_right dimensionOneRosserSecondLevelThreshold
        (max (S ^ (50 : Nat)) (C ^ (24 : Nat)))).trans
        ((le_max_right L0 _).trans hlarge))
  have hCNonneg : 0 <= C := by
    dsimp only [C]
    positivity
  have hrootNonneg : 0 <= L ^ (1 / 24 : Real) :=
    Real.rpow_nonneg hLPos.le _
  have hrootPow : (L ^ (1 / 24 : Real)) ^ (24 : Nat) = L := by
    convert Real.rpow_inv_natCast_pow (n := 24) hLPos.le
      (by norm_num : (24 : Nat) ≠ 0) using 1; norm_num
  have hsmall : C <= L ^ (1 / 24 : Real) := by
    apply (pow_le_pow_iff_left₀ hCNonneg hrootNonneg
      (by norm_num : (24 : Nat) ≠ 0)).mp
    rwa [hrootPow]
  refine ⟨{
    s0 := s0
    hcutoff := hcutoff
    hsTail := hs0S
    hsource := ?_
    hLExp := hLExp
    hgate := hgate
    hgrowth := hgrowth
    hsmall := ?_ }⟩
  · simpa only [L, A] using hsource
  · simpa only [C, L] using hsmall

/-- Above the same threshold, the selected cutoff has the exact direct or
ready comparison with every current coordinate. -/
theorem exists_dimensionOneRosserSourceAllStateData_threshold
    {K S : Real} (hK : 0 <= K)
    (hS : Real.exp 5000 + 1 <= S) :
    exists Lambda : Real, Real.exp 1 <= Lambda /\
      forall {level s : Real}, 2 <= level ->
        Lambda <= Real.log level ->
        Nonempty (DimensionOneRosserSourceAllStateData K S level s) := by
  obtain ⟨Lambda, hLambda, hCutoff⟩ :=
    exists_dimensionOneRosserSourceCutoffData_threshold hK hS
  refine ⟨Lambda, hLambda, ?_⟩
  intro level s hlevel hlarge
  obtain ⟨cutoff⟩ := hCutoff hlevel hlarge
  refine ⟨{ cutoff := cutoff, direct_or_ready := ?_ }⟩
  by_cases hdirect : cutoff.s0 <= s
  · exact Or.inl hdirect
  · exact Or.inr (lt_of_not_ge hdirect)

/--
The global strict decimal density estimate supplies the weak ratio family from source cutoff
data, independently of the coordinate branch.
-/
theorem dimensionOneRosserSourceCutoffData_densityRatio
    (P : Finset Nat) {K S level z : Real}
    (hGlobalRatio : forall (Q : Finset Nat) (w x : Real),
      (forall p, p ∈ Q -> p.Prime) ->
      (forall p, p ∈ Q -> not (p ∣ 10)) ->
      2 <= w -> w < x ->
      sieveDensityBelow Q (fun p => (p : Real)⁻¹) w /
          sieveDensityBelow Q (fun p => (p : Real)⁻¹) x <
        (Real.log x / Real.log w) * (1 + K / Real.log w))
    (hprime : forall p, p ∈ P -> p.Prime)
    (hdecimal : forall p, p ∈ P -> not (p ∣ 10))
    (data : DimensionOneRosserSourceCutoffData K S level) :
    forall u : Real,
      level ^ (1 / data.s0) <= u -> u < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) u /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log u) * (1 + K / Real.log u) := by
  intro u hu huz
  exact (hGlobalRatio P u z hprime hdecimal
    (data.hcutoff.trans hu) huz).le

end PrimesRestrictedDigits
