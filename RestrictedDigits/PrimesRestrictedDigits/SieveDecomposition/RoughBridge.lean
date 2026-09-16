import PrimesRestrictedDigits.SieveDecomposition.Definitions
import PrimesRestrictedDigits.PrimeNumberTheorem.MaynardBuchstab

/-!
# Ambient sifted-carrier bridge

This file identifies the paper's ambient `S(B_d,z)` carrier with the positive
strict rough carrier already bounded by the Buchstab estimate.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 137--141, especially Eq. (6.7).
-/

namespace PrimesRestrictedDigits

theorem strictSiftedCarrier_maynardAmbientCarrier_eq
    {X z : Real} (hz : 2 ≤ z) :
    strictSiftedCarrier (maynardAmbientCarrier X) z =
      maynardStrictRoughCarrier X z := by
  classical
  ext n
  simp only [mem_strictSiftedCarrier, mem_maynardAmbientCarrier,
    mem_maynardStrictRoughCarrier]
  constructor
  · rintro ⟨hnX, hrough⟩
    have hn0 : n ≠ 0 := by
      intro hn
      subst n
      have hzlt : z < 2 := strictRoughPredicate_zero.mp hrough
      linarith
    exact ⟨Nat.one_le_iff_ne_zero.mpr hn0, hnX, hrough⟩
  · rintro ⟨_, hnX, hrough⟩
    exact ⟨hnX, hrough⟩

theorem strictSiftedCarrier_sieveDilation_maynardAmbientCarrier_eq
    {X z : Real} (d : PNat) (hz : 2 ≤ z) :
    strictSiftedCarrier (sieveDilation (maynardAmbientCarrier X) d) z =
      maynardStrictRoughCarrier (X / (d : Real)) z := by
  rw [sieveDilation_maynardAmbientCarrier,
    strictSiftedCarrier_maynardAmbientCarrier_eq hz]

theorem card_strictSiftedCarrier_sieveDilation_maynardAmbientCarrier
    {X z : Real} (d : PNat) (hz : 2 ≤ z) :
    (strictSiftedCarrier
        (sieveDilation (maynardAmbientCarrier X) d) z).card =
      maynardStrictRoughCount (X / (d : Real)) z := by
  rw [strictSiftedCarrier_sieveDilation_maynardAmbientCarrier_eq d hz,
    maynardStrictRoughCount]

end PrimesRestrictedDigits
