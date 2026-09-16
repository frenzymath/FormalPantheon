import PrimesRestrictedDigits.SieveAsymptotics.SectionSixSourceTerminalFiber
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Sublists

/-!
# Variable-modulus incidence for Section 6 terminal states

Prime-factor sublists count the possible positive divisor moduli of one represented integer.
Combining that count with the fixed-modulus fiber bound gives the band-specific
variable-modulus state incidence bound.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Products of all positional prime-factor sublists of `n`. Repeated prime
occurrences remain distinct before the final deduplication. -/
noncomputable def sectionSixDivisorCandidates (n : Nat) : Finset Nat := by
  classical
  exact (n.primeFactorsList.sublists.map List.prod).toFinset

theorem mem_sectionSixDivisorCandidates_of_dvd
    {D n : Nat} (hn : n ≠ 0) (hD : D ∣ n) :
    D ∈ sectionSixDivisorCandidates n := by
  classical
  have hDne : D ≠ 0 := ne_zero_of_dvd_ne_zero hn hD
  unfold sectionSixDivisorCandidates
  rw [List.mem_toFinset]
  apply List.mem_map.mpr
  exact ⟨D.primeFactorsList,
    List.mem_sublists.mpr (Nat.primeFactorsList_sublist_of_dvd hD hn),
    Nat.prod_primeFactorsList hDne⟩

theorem card_sectionSixDivisorCandidates_le_two_pow_factorLength
    (n : Nat) :
    (sectionSixDivisorCandidates n).card ≤
      2 ^ n.primeFactorsList.length := by
  classical
  calc
    (sectionSixDivisorCandidates n).card ≤
        (n.primeFactorsList.sublists.map List.prod).length := by
      unfold sectionSixDivisorCandidates
      exact List.toFinset_card_le
        (l := n.primeFactorsList.sublists.map List.prod)
    _ = n.primeFactorsList.sublists.length := by simp
    _ = 2 ^ n.primeFactorsList.length := List.length_sublists _

theorem card_sectionSixDivisorCandidates_le_two_pow_ceil_inv_delta
    {X delta : Real} {n : Nat}
    (hX : 1 < X) (hdelta : 0 < delta) (hn : n ≠ 0)
    (hnX : (n : Real) ≤ X)
    (hnRough : weakRoughPredicate (X ^ delta) n) :
    (sectionSixDivisorCandidates n).card ≤
      2 ^ Nat.ceil (1 / delta) := by
  have hlength : n.primeFactorsList.length ≤ Nat.ceil (1 / delta) := by
    apply primeFactorsList_length_le_ceil_inv_delta hX hdelta hn hnX
    intro q hq
    exact hnRough q (Nat.prime_of_mem_primeFactorsList hq)
      (Nat.dvd_of_mem_primeFactorsList hq)
  exact (card_sectionSixDivisorCandidates_le_two_pow_factorLength n).trans
    (Nat.pow_le_pow_right (by norm_num) hlength)

/-- A duplicate-free state list with at most `fiberBound` states at each key
has at most `fiberBound * divisorBound` selected states whose key divides one
fixed positive integer. -/
theorem length_nodup_key_divisorFiber_le
    {alpha : Type*}
    (states : List alpha) (hstates : states.Nodup)
    (key : alpha → Nat) {n fiberBound divisorBound : Nat}
    (hn : n ≠ 0) (predicate : alpha → Bool)
    (hfixed : ∀ D,
      (states.filter fun state => key state = D).length ≤ fiberBound)
    (hcandidates :
      (sectionSixDivisorCandidates n).card ≤ divisorBound) :
    (states.filter fun state =>
      predicate state && decide (key state ∣ n)).length ≤
        fiberBound * divisorBound := by
  classical
  let selectedList := states.filter fun state =>
    predicate state && decide (key state ∣ n)
  let selected : Finset alpha := selectedList.toFinset
  have hselectedCard : selected.card = selectedList.length := by
    dsimp only [selected, selectedList]
    exact List.toFinset_card_of_nodup (hstates.filter _)
  have hmaps : ∀ state ∈ selected,
      key state ∈ sectionSixDivisorCandidates n := by
    intro state hstate
    have hstateList : state ∈ selectedList := List.mem_toFinset.mp hstate
    have hselected := (List.mem_filter.mp hstateList).2
    have hkeyDvd : key state ∣ n :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp hselected).2
    exact mem_sectionSixDivisorCandidates_of_dvd hn hkeyDvd
  have hfiber : ∀ D ∈ sectionSixDivisorCandidates n,
      (selected.filter fun state => key state = D).card ≤ fiberBound := by
    intro D _hD
    have hsubset :
        selected.filter (fun state => key state = D) ⊆
          (states.filter fun state => key state = D).toFinset := by
      intro state hstate
      have hstateData := Finset.mem_filter.mp hstate
      have hstateList : state ∈ selectedList :=
        List.mem_toFinset.mp hstateData.1
      have hstateStates : state ∈ states :=
        (List.mem_filter.mp hstateList).1
      apply List.mem_toFinset.mpr
      exact List.mem_filter.mpr
        ⟨hstateStates, decide_eq_true hstateData.2⟩
    calc
      (selected.filter fun state => key state = D).card ≤
          ((states.filter fun state => key state = D).toFinset).card :=
        Finset.card_le_card hsubset
      _ = (states.filter fun state => key state = D).length :=
        List.toFinset_card_of_nodup (hstates.filter _)
      _ ≤ fiberBound := hfixed D
  have hpartition : selected.card ≤
      fiberBound * (sectionSixDivisorCandidates n).card :=
    Finset.card_le_mul_card_image_of_maps_to hmaps fiberBound hfiber
  change selectedList.length ≤ fiberBound * divisorBound
  rw [← hselectedCard]
  exact hpartition.trans (Nat.mul_le_mul_left fiberBound hcandidates)

theorem length_sectionSixSourceBandTerminalStates_divisorFiber_le
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell → Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length) (hdelta : 0 < delta)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (n : Nat) (hn : n ≠ 0)
    (hnX : (n : Real) ≤ ((10 ^ length : Nat) : Real))
    (hnRough : weakRoughPredicate
      (((10 ^ length : Nat) : Real) ^ delta) n)
    (predicate : SectionSixAnyState band ell → Bool) :
    ((sectionSixSourceBandTerminalStates region hepsilon hepsilonSmall
      hlength hdeltaGap band).filter fun state =>
        predicate state && decide (state.1 ∣ n)).length ≤
      (5 * (Nat.ceil (1 / delta)) ^ ell) *
        2 ^ Nat.ceil (1 / delta) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have hXNat : 1 < 10 ^ length :=
    Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast hXNat
  apply length_nodup_key_divisorFiber_le
    (sectionSixSourceBandTerminalStates region hepsilon hepsilonSmall
      hlength hdeltaGap band)
    (sectionSixSourceBandTerminalStates_nodup region hepsilon hepsilonSmall
      hlength hdeltaGap band)
    (fun state => state.1) hn predicate
  · intro D
    exact length_sectionSixSourceBandTerminalStates_modulusFiber_le region
      hepsilon hepsilonSmall hlength hdelta hdeltaGap band D
  · exact card_sectionSixDivisorCandidates_le_two_pow_ceil_inv_delta
      hX hdelta hn (by simpa only [X] using hnX)
      (by simpa only [X] using hnRough)

end

end PrimesRestrictedDigits
