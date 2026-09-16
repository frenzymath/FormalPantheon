import Waring.Analytic.HuaSmallPrimePower
import Waring.Analytic.WeilChenAdapter
import Waring.Analytic.ChenSeven

/-!
# Unconditional form of Chen's Lemma 7

The Hua small-prime-power estimate and the Weil large-prime estimate discharge
the two analytic hypotheses of the source-shaped theorem.
-/

namespace Waring.Analytic

open scoped BigOperators

/-- Chen's Lemma 7 with both polynomial-sum inputs proved. -/
theorem chen_lemma_seven_unconditional
    (q : Nat) [NeZero q] (a : Nat) (z : Real) (P : Nat)
    (hPThreshold : (10 : Real) ^ 150 <= P)
    (hqLower : (P : Real) ^ (1 / 2 : Real) <= q)
    (hqUpper : (q : Real) <= (P : Real) ^ (26 / 25 : Real))
    (ha : IsUnit (a : ZMod q))
    (hz : |z| <= 1 / (10 * (q : Real) * (P : Real) ^ 4)) :
    ‖∑ i ∈ Finset.range P,
        Complex.exp
          (2 * Real.pi * Complex.I *
            (((a : Real) / q + z) * (((1 + i : Nat) : Real) ^ 5)))‖ <=
      (P : Real) ^ (24 / 25 : Real) :=
  chen_lemma_seven chenFiveHuaSmallPrimePowerBound
    chenFiveLargePrimeFieldBound q a z P hPThreshold hqLower hqUpper ha hz

end Waring.Analytic
