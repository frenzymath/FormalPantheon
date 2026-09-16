import PrimesRestrictedDigits.Digits.ZeroPrimeCount
import PrimesRestrictedDigits.SieveDecomposition.FixedLengthPrimeBridge

/-!
# Excluded-zero block to fixed-length prime bridge

The exact positive digit-length block for excluded zero is the corresponding
padded fixed-length carrier.  Keeping this equality in a sieve-layer adapter
avoids importing sieve definitions into the digit foundation.
-/

namespace PrimesRestrictedDigits

noncomputable section

theorem zeroRestrictedPrimeBlock_eq_paddedRestrictedPrimes (index : ℕ) :
    zeroRestrictedPrimeBlock index =
      paddedRestrictedPrimes (0 : Fin 10) (index + 1) := by
  rw [zeroRestrictedPrimeBlock, paddedRestrictedPrimes,
    zeroRestrictedNumberBlock_eq_paddedRestrictedNumbers]

end

end PrimesRestrictedDigits
