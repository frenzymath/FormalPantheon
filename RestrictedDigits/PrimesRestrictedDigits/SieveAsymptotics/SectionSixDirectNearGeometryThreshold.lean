import PrimesRestrictedDigits.SieveAsymptotics.TypeIILogLogWidthAbsorption

/-!
# Eventual direct near geometry

The three length-dependent geometry premises used by the direct stable-target argument are
bundled into one decimal threshold. Fixed small-epsilon and delta-gap hypotheses remain
outside this result.
-/

open Filter

namespace PrimesRestrictedDigits

noncomputable section

/-- The square, margin, and global direct-near widths are eventually below
their fixed positive budgets. -/
theorem exists_sectionSixDirectNearGeometryThreshold
    (delta epsilon : Real) (hdelta : 0 < delta)
    (hepsilon : 0 < epsilon) (ell : Nat) :
    ∃ length0 : Nat, 1 <= length0 ∧
      ∀ length : Nat, length0 <= length ->
        let rho : Real := majorArcM2LogLogDelta (10 ^ length)
        let M : Nat := Nat.ceil (2 / delta)
        rho ^ 2 < delta ∧
          2 * rho <= delta / 2 ∧
          rho ^ 2 + (((ell + M : Nat) : Real) * rho) <= epsilon := by
  let M : Nat := Nat.ceil (2 / delta)
  let K : Real := ((ell + M : Nat) : Real)
  let rho : Nat -> Real := fun length =>
    majorArcM2LogLogDelta (10 ^ length)
  have hrho : Tendsto rho atTop (nhds 0) := by
    simpa only [rho] using tendsto_majorArcM2LogLogDelta_powTen
  have hrhoSq : Tendsto (fun length => rho length ^ 2) atTop (nhds 0) := by
    simpa using hrho.pow 2
  have hmargin : Tendsto (fun length => 2 * rho length) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hrho
  have hlinear : Tendsto (fun length => K * rho length) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hrho
  have hglobal : Tendsto
      (fun length => rho length ^ 2 + K * rho length) atTop (nhds 0) := by
    simpa using hrhoSq.add hlinear
  have hevent : ∀ᶠ length : Nat in atTop,
      rho length ^ 2 < delta ∧
        2 * rho length < delta / 2 ∧
        rho length ^ 2 + K * rho length < epsilon := by
    filter_upwards [hrhoSq.eventually_lt_const hdelta,
      hmargin.eventually_lt_const (by positivity : 0 < delta / 2),
      hglobal.eventually_lt_const hepsilon] with length hsq hmarginAt hglobalAt
    exact ⟨hsq, hmarginAt, hglobalAt⟩
  obtain ⟨length1, hlength1⟩ := eventually_atTop.mp hevent
  refine ⟨max 1 length1, le_max_left _ _, ?_⟩
  intro length hlength
  have hAt := hlength1 length ((le_max_right 1 length1).trans hlength)
  dsimp only
  simpa only [rho, K, M] using ⟨hAt.1, hAt.2.1.le, hAt.2.2.le⟩

end

end PrimesRestrictedDigits
