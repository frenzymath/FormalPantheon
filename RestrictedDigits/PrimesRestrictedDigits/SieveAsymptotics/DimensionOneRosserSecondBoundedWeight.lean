import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayFiniteTails
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserLogTransform
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSecondPrefactor
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSecondWeight

/-!
# Natural-domain regularity of the second Rosser weight

This glues the bounded and large-coordinate parts of Iwaniec's Eq. (8.11) and transports the
resulting antitonicity through the Buchstab coordinate.
-/

open Set

namespace PrimesRestrictedDigits

/-- Glue antitonicity on two closed intervals sharing one endpoint. -/
theorem dimensionOneRosserAntitoneOn_Icc_of_split
    {f : Real -> Real} {a u b : Real} (hau : a <= u) (hub : u <= b)
    (hleft : AntitoneOn f (Icc a u))
    (hright : AntitoneOn f (Icc u b)) :
    AntitoneOn f (Icc a b) := by
  intro x hx y hy hxy
  by_cases hyu : y <= u
  · exact hleft ⟨hx.1, hxy.trans hyu⟩ ⟨hx.1.trans hxy, hyu⟩ hxy
  by_cases hux : u <= x
  · exact hright ⟨hux, hx.2⟩ ⟨hux.trans hxy, hy.2⟩ hxy
  have hxu : x <= u := le_of_not_ge hux
  have huy : u <= y := le_of_not_ge hyu
  exact (hright ⟨le_rfl, hub⟩ ⟨huy, hy.2⟩ huy).trans
    (hleft ⟨hx.1, hxu⟩ ⟨hau, le_rfl⟩ hxu)

/-- The target-plus second kernel is antitone on the bounded range. -/
theorem dimensionOneRosserPlusSecondKernel_antitoneOn_bounded
    {L u : Real} (hu : 3 <= u) (hgrowth : 9792 * u ^ 52 <= L) :
    AntitoneOn (dimensionOneRosserPlusSecondKernel L) (Icc 3 u) := by
  have hu0 : 0 < u := by linarith
  have hL : 0 < L :=
    (mul_pos (by norm_num) (pow_pos hu0 52)).trans_le hgrowth
  have hprefactor :=
    (dimensionOneRosserSecondPrefactor_strictAntiOn (by linarith) hgrowth).antitoneOn
  intro x hx y hy hxy
  rw [dimensionOneRosserPlusSecondKernel_eq_prefactor,
    dimensionOneRosserPlusSecondKernel_eq_prefactor]
  have hfactor := hprefactor
    ⟨by linarith [hx.1], hx.2⟩ ⟨by linarith [hy.1], hy.2⟩ hxy
  have hdelay := dimensionOneDelayScaledMinus_antitoneOn
    (show x - 1 ∈ Ici (2 : Real) by change 2 <= x - 1; linarith [hx.1])
    (show y - 1 ∈ Ici (2 : Real) by change 2 <= y - 1; linarith [hy.1])
    (by linarith)
  exact mul_le_mul hfactor hdelay
    (dimensionOneDelayScaledMinus_pos (by linarith [hy.1])).le
    (dimensionOneRosserSecondPrefactor_pos hL).le

/-- The target-minus second kernel is antitone on the bounded range. -/
theorem dimensionOneRosserMinusSecondKernel_antitoneOn_bounded
    {L u : Real} (hu : 2 <= u) (hgrowth : 9792 * u ^ 52 <= L) :
    AntitoneOn (dimensionOneRosserMinusSecondKernel L) (Icc 2 u) := by
  have hu0 : 0 < u := by linarith
  have hL : 0 < L :=
    (mul_pos (by norm_num) (pow_pos hu0 52)).trans_le hgrowth
  have hprefactor :=
    (dimensionOneRosserSecondPrefactor_strictAntiOn hu hgrowth).antitoneOn
  intro x hx y hy hxy
  rw [dimensionOneRosserMinusSecondKernel_eq_prefactor,
    dimensionOneRosserMinusSecondKernel_eq_prefactor]
  have hfactor := hprefactor hx hy hxy
  have hdelay := dimensionOneDelayScaledPlus_antitoneOn
    (show x - 1 ∈ Ici (1 : Real) by change 1 <= x - 1; linarith [hx.1])
    (show y - 1 ∈ Ici (1 : Real) by change 1 <= y - 1; linarith [hy.1])
    (by linarith)
  exact mul_le_mul hfactor hdelay
    (dimensionOneDelayScaledPlus_pos (by linarith [hy.1])).le
    (dimensionOneRosserSecondPrefactor_pos hL).le

/-- The target-plus second kernel is antitone on its full direct domain. -/
theorem dimensionOneRosserPlusSecondKernel_antitoneOn_sourceDomain
    {L s0 : Real}
    (hsplice : 2 * dimensionOneRosserSecondSplice <= s0)
    (hcap : s0 ^ 50 <= L)
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= L) :
    AntitoneOn (dimensionOneRosserPlusSecondKernel L) (Icc 3 s0) := by
  have hUOne := one_le_dimensionOneRosserSecondSplice
  have hU3 : 3 <= dimensionOneRosserSecondSplice := by
    unfold dimensionOneRosserSecondSplice
    nlinarith [Real.exp_pos (5000 : Real)]
  have hUs0 : dimensionOneRosserSecondSplice < s0 := by
    nlinarith [hUOne]
  have hL : 0 < L := dimensionOneRosserSecondLevelThreshold_pos.trans_le hgrowth
  have hlocalGrowth : 9792 * dimensionOneRosserSecondSplice ^ 52 <= L := by
    simpa [dimensionOneRosserSecondLevelThreshold] using hgrowth
  apply dimensionOneRosserAntitoneOn_Icc_of_split hU3 hUs0.le
  · exact dimensionOneRosserPlusSecondKernel_antitoneOn_bounded hU3 hlocalGrowth
  · apply dimensionOneRosserPlusSecondKernel_antitoneOn hL
    · unfold dimensionOneRosserSecondSplice
      linarith
    · exact hUs0
    · exact hcap

/-- The target-minus second kernel is antitone on its full direct domain. -/
theorem dimensionOneRosserMinusSecondKernel_antitoneOn_sourceDomain
    {L s0 : Real}
    (hsplice : 2 * dimensionOneRosserSecondSplice <= s0)
    (hcap : s0 ^ 50 <= L)
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= L) :
    AntitoneOn (dimensionOneRosserMinusSecondKernel L) (Icc 2 s0) := by
  have hUOne := one_le_dimensionOneRosserSecondSplice
  have hU2 : 2 <= dimensionOneRosserSecondSplice := by
    unfold dimensionOneRosserSecondSplice
    nlinarith [Real.exp_pos (5000 : Real)]
  have hUs0 : dimensionOneRosserSecondSplice < s0 := by
    nlinarith [hUOne]
  have hL : 0 < L := dimensionOneRosserSecondLevelThreshold_pos.trans_le hgrowth
  have hlocalGrowth : 9792 * dimensionOneRosserSecondSplice ^ 52 <= L := by
    simpa [dimensionOneRosserSecondLevelThreshold] using hgrowth
  apply dimensionOneRosserAntitoneOn_Icc_of_split hU2 hUs0.le
  · exact dimensionOneRosserMinusSecondKernel_antitoneOn_bounded hU2 hlocalGrowth
  · apply dimensionOneRosserMinusSecondKernel_antitoneOn hL
    · unfold dimensionOneRosserSecondSplice
      linarith
    · exact hUs0
    · exact hcap

/-- Full source-domain regularity of the target-plus composed second weight. -/
theorem dimensionOneRosserPlusSecondWeight_properties_sourceDomain
    {level z s s0 : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 3 <= s)
    (hss0 : s < s0)
    (hsplice : 2 * dimensionOneRosserSecondSplice <= s0)
    (hcap : s0 ^ 50 <= Real.log level)
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= Real.log level) :
    (∀ x ∈ Icc (level ^ (1 / s0)) z,
        0 <= dimensionOneRosserPlusSecondWeight level x) ∧
      ContinuousOn (dimensionOneRosserPlusSecondWeight level)
        (Icc (level ^ (1 / s0)) z) ∧
      MonotoneOn (dimensionOneRosserPlusSecondWeight level)
        (Icc (level ^ (1 / s0)) z) := by
  have hanti :=
    (dimensionOneRosserPlusSecondKernel_antitoneOn_sourceDomain
      hsplice hcap hgrowth).mono
      (show Icc s s0 ⊆ Icc (3 : Real) s0 by
        intro t ht
        exact ⟨hsLower.trans ht.1, ht.2⟩)
  change (∀ x ∈ Icc (level ^ (1 / s0)) z,
      0 <= dimensionOneRosserPlusSecondKernel (Real.log level)
        (buchstabArgument level x + 1)) ∧
    ContinuousOn
      (fun x => dimensionOneRosserPlusSecondKernel (Real.log level)
        (buchstabArgument level x + 1)) (Icc (level ^ (1 / s0)) z) ∧
    MonotoneOn
      (fun x => dimensionOneRosserPlusSecondKernel (Real.log level)
        (buchstabArgument level x + 1)) (Icc (level ^ (1 / s0)) z)
  exact dimensionOneRosserSecondWeight_properties_of_antitoneOn
    dimensionOneRosserPlusSecondKernel
    dimensionOneRosserPlusSecondKernel_pos
    dimensionOneRosserPlusSecondKernel_continuousOn hlevel hz hs
    (by linarith) hss0 hanti

/-- Full source-domain regularity of the target-minus composed second weight. -/
theorem dimensionOneRosserMinusSecondWeight_properties_sourceDomain
    {level z s s0 : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hss0 : s < s0)
    (hsplice : 2 * dimensionOneRosserSecondSplice <= s0)
    (hcap : s0 ^ 50 <= Real.log level)
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= Real.log level) :
    (∀ x ∈ Icc (level ^ (1 / s0)) z,
        0 <= dimensionOneRosserMinusSecondWeight level x) ∧
      ContinuousOn (dimensionOneRosserMinusSecondWeight level)
        (Icc (level ^ (1 / s0)) z) ∧
      MonotoneOn (dimensionOneRosserMinusSecondWeight level)
        (Icc (level ^ (1 / s0)) z) := by
  have hanti :=
    (dimensionOneRosserMinusSecondKernel_antitoneOn_sourceDomain
      hsplice hcap hgrowth).mono
      (show Icc s s0 ⊆ Icc (2 : Real) s0 by
        intro t ht
        exact ⟨hsLower.trans ht.1, ht.2⟩)
  change (∀ x ∈ Icc (level ^ (1 / s0)) z,
      0 <= dimensionOneRosserMinusSecondKernel (Real.log level)
        (buchstabArgument level x + 1)) ∧
    ContinuousOn
      (fun x => dimensionOneRosserMinusSecondKernel (Real.log level)
        (buchstabArgument level x + 1)) (Icc (level ^ (1 / s0)) z) ∧
    MonotoneOn
      (fun x => dimensionOneRosserMinusSecondKernel (Real.log level)
        (buchstabArgument level x + 1)) (Icc (level ^ (1 / s0)) z)
  exact dimensionOneRosserSecondWeight_properties_of_antitoneOn
    dimensionOneRosserMinusSecondKernel
    dimensionOneRosserMinusSecondKernel_pos
    dimensionOneRosserMinusSecondKernel_continuousOn hlevel hz hs
    (by linarith) hss0 hanti

end PrimesRestrictedDigits
