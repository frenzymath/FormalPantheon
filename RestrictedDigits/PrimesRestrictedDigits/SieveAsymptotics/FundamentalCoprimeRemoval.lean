import PrimesRestrictedDigits.SieveDecomposition.RoughSmoothFactorization
import PrimesRestrictedDigits.SieveAsymptotics.DecimalAmbientBoundingSieve
import PrimesRestrictedDigits.PrimeNumberTheorem.MaynardBuchstab
import PrimesRestrictedDigits.TypeI.PropositionSevenOne
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Coprime removal after strict sifting

This records the finite filtered/unfiltered bridge and the exact decimal density relation used
after the two coprime fundamental-sieve splits.
-/

namespace PrimesRestrictedDigits

noncomputable section

theorem strictSiftedCarrier_sieveDilation_filter_coprime_ten_eq
    (C : Finset Nat) (d : PNat) {z : Real}
    (hz : 5 <= z) (hd : (d : Nat).Coprime 10) :
    strictSiftedCarrier
        (sieveDilation (C.filter (fun n => n.Coprime 10)) d) z =
      strictSiftedCarrier (sieveDilation C d) z := by
  classical
  ext n
  rw [mem_strictSiftedCarrier, mem_strictSiftedCarrier]
  constructor
  · rintro ⟨hn, hrough⟩
    have hfiltered := mem_sieveDilation.mp hn
    exact ⟨mem_sieveDilation.mpr (Finset.mem_filter.mp hfiltered).1, hrough⟩
  · rintro ⟨hn, hrough⟩
    have hcarrier := mem_sieveDilation.mp hn
    have hnCoprime : n.Coprime 10 :=
      strictRoughPredicate_coprime_ten hz hrough
    have hfiltered : n * (d : Nat) ∈ C.filter (fun a => a.Coprime 10) :=
      Finset.mem_filter.mpr ⟨hcarrier,
        Nat.coprime_mul_iff_left.mpr ⟨hnCoprime, hd⟩⟩
    exact ⟨mem_sieveDilation.mpr hfiltered, hrough⟩

theorem maynardStrictRoughCarrier_mem_coprime_ten
    {Y z : Real} (hz : 5 <= z) {d : Nat}
    (hd : d ∈ maynardStrictRoughCarrier Y z) : d.Coprime 10 := by
  exact strictRoughPredicate_coprime_ten hz
    (mem_maynardStrictRoughCarrier.mp hd).2.2

theorem five_halves_mul_typeIProgressionDensity
    (digit : Fin 10) :
    (5 / 2 : Rat) * typeIProgressionDensity digit =
      restrictedDigitDensity digit := by
  rw [typeIProgressionDensity]
  have htotient : Nat.totient 10 = 4 := by decide
  rw [htotient]
  ring

end

end PrimesRestrictedDigits
