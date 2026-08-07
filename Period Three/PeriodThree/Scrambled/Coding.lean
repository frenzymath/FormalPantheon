module

public import PeriodThree.Statement

meta import all Mathlib.Tactic.Linarith -- shake: keep (used by square-index arithmetic)
meta import all Mathlib.Tactic.Ring -- shake: keep (used by square-index identities)

/-!
# Square-index codes for Li-Yorke itineraries

This file defines the repeated-bit symbolic schedule used in the documented
replacement for the density codes of [LY75, Appendix 2, pp. 990-992].  It is
purely combinatorial; real intervals and the dynamical interpretation live in a
separate module.
 -/

@[expose] public section

namespace PeriodThree

/-- A symbolic interval in the Appendix 2 itinerary.  `base` denotes `L`, while
`lower m` and `upper m` denote the two sides of the reversing bridge
[LY75, Appendix 2, pp. 990-992]. -/
inductive CodeTag where
  /-- The distinguished `K` interval tag. -/
  | k
  /-- The base `L` interval tag. -/
  | base
  /-- A lower endpoint tag at level `m`. -/
  | lower (m : ℕ)
  /-- An upper endpoint tag at level `m`. -/
  | upper (m : ℕ)
  deriving DecidableEq

namespace CodeTag

/-- The tags whose eventual interpretation is contained in the base interval
`L` of [LY75, Appendix 2, p. 991]. -/
def IsInBase : CodeTag → Prop
  | .k => False
  | _ => True

/-- The symbolic cover edges used by the square-index schedule.  These are the
three elementary covers and the alternating bridge in [LY75, Appendix 2,
pp. 991-992]. -/
def Follows : CodeTag → CodeTag → Prop
  | .k, target => target.IsInBase
  | .base, _ => True
  | .lower (.succ m), .upper n => n = m
  | .upper (.succ m), .lower n => n = m
  | .upper 0, .k => True
  | _, _ => False

end CodeTag

/-- The first root of the `t`th universal consecutive-square block in the D6
replacement for [LY75, Appendix 2, pp. 990-992]. -/
def universalRoot (t : ℕ) : ℕ := 3 * (t + 1)

/-- The first square time of the `t`th universal block in the D6 replacement
for [LY75, Appendix 2, pp. 990-992]. -/
def universalTime (t : ℕ) : ℕ := (universalRoot t) ^ 2

/-- The square time at which schedule number `t` records a code bit in the D6
replacement for [LY75, Appendix 2, pp. 990-992]. -/
def encodingTime (t : ℕ) : ℕ := (3 * t + 2) ^ 2

/-- The total repeated-bit schedule used in place of the density family in
[LY75, Appendix 2, conditions (A.1)-(A.4), pp. 990-991]. -/
def codeTag (beta : ℕ → Bool) (n : ℕ) : CodeTag :=
  let r := n.sqrt
  let j := n - r ^ 2
  if 3 ≤ r ∧ r % 3 = 0 then
    if j = 0 then .k
    else if j % 2 = 1 then .lower (2 * r - j)
    else .upper (2 * r - j)
  else if 3 ≤ r ∧ r % 3 = 1 ∧ j = 0 then .k
  else if r % 3 = 2 ∧ j = 0 ∧ beta (Nat.unpair ((r - 2) / 3)).1 = true then .k
  else .base

private theorem universalRoot_pos (t : ℕ) : 0 < universalRoot t := by
  simp [universalRoot]

private theorem universalRoot_mod (t : ℕ) : universalRoot t % 3 = 0 := by
  simp [universalRoot]

private theorem encodingRoot_mod (t : ℕ) : (3 * t + 2) % 3 = 2 := by
  omega

/-- The two initial square-root blocks contain only the base tag in the D6
schedule replacing [LY75, Appendix 2, pp. 990-992]. -/
theorem codeTag_of_sqrt_lt_two (beta : ℕ → Bool) {n : ℕ} (hn : n.sqrt < 2) :
    codeTag beta n = .base := by
  have hr : n.sqrt = 0 ∨ n.sqrt = 1 := by omega
  rcases hr with hr | hr <;> simp [codeTag, hr]

/-- Every scheduled time has one of the four symbolic tag forms used for
[LY75, Appendix 2, pp. 990-992]. -/
theorem codeTag_cases (beta : ℕ → Bool) (n : ℕ) :
    codeTag beta n = .k ∨ codeTag beta n = .base ∨
      (∃ m : ℕ, codeTag beta n = .lower m) ∨ ∃ m : ℕ, codeTag beta n = .upper m := by
  cases codeTag beta n <;> simp

/-- A universal block starts in the distinguished interval `K`, implementing
the common blocks of [LY75, Appendix 2, pp. 991-992]. -/
theorem codeTag_universalStart (beta : ℕ → Bool) (t : ℕ) :
    codeTag beta (universalTime t) = .k := by
  have hr3 : 3 ≤ universalRoot t := by simp [universalRoot]
  simp [codeTag, universalTime, hr3, universalRoot_mod]

/-- The interior of a universal block alternates down the two reversing
interval nests from [LY75, Appendix 2, pp. 991-992]. -/
theorem codeTag_universalBridge (beta : ℕ → Bool) (t : ℕ) {j : ℕ}
    (hj0 : 0 < j) (hj : j ≤ 2 * universalRoot t) :
    codeTag beta (universalTime t + j) =
      if j % 2 = 1 then .lower (2 * universalRoot t - j)
      else .upper (2 * universalRoot t - j) := by
  have hsqrt : (universalTime t + j).sqrt = universalRoot t := by
    apply Nat.sqrt_add_eq'
    omega
  have hr3 : 3 ≤ universalRoot t := by simp [universalRoot]
  have hdiff : universalTime t + j - universalRoot t ^ 2 = j := by
    simp [universalTime]
  unfold codeTag
  dsimp only
  rw [hsqrt]
  rw [hdiff, if_pos ⟨hr3, universalRoot_mod t⟩, if_neg (Nat.ne_of_gt hj0)]

/-- The square immediately after a universal bridge returns to `K`, as required
by the itinerary in [LY75, Appendix 2, pp. 991-992]. -/
theorem codeTag_universalEnd (beta : ℕ → Bool) (t : ℕ) :
    codeTag beta ((universalRoot t + 1) ^ 2) = .k := by
  have hr3 : 3 ≤ universalRoot t + 1 := by
    unfold universalRoot
    omega
  have hrmod : (universalRoot t + 1) % 3 = 1 := by
    simp [universalRoot]
  simp [codeTag, hr3, hrmod]

/-- An encoding square records precisely the selected bit in the D6 replacement
for the parameter codes of [LY75, Appendix 2, pp. 990-991]. -/
theorem codeTag_encodingTime (beta : ℕ → Bool) (t : ℕ) :
    codeTag beta (encodingTime t) =
      if beta (Nat.unpair t).1 = true then .k else .base := by
  simp [codeTag, encodingTime, encodingRoot_mod]

private def blockTag (beta : ℕ → Bool) (r j : ℕ) : CodeTag :=
  if 3 ≤ r ∧ r % 3 = 0 then
    if j = 0 then .k
    else if j % 2 = 1 then .lower (2 * r - j)
    else .upper (2 * r - j)
  else if 3 ≤ r ∧ r % 3 = 1 ∧ j = 0 then .k
  else if r % 3 = 2 ∧ j = 0 ∧ beta (Nat.unpair ((r - 2) / 3)).1 = true then .k
  else .base

private theorem blockTag_follows_succ (beta : ℕ → Bool) {r j : ℕ}
    (hj : j < 2 * r) :
    (blockTag beta r j).Follows (blockTag beta r (j + 1)) := by
  by_cases hu : 3 ≤ r ∧ r % 3 = 0
  · have hjnext : j + 1 ≠ 0 := by omega
    simp only [blockTag, if_pos hu]
    by_cases hj0 : j = 0
    · simp [hj0, CodeTag.Follows, CodeTag.IsInBase]
    · rw [if_neg hj0, if_neg hjnext]
      have hindex : 2 * r - j = (2 * r - (j + 1)) + 1 := by omega
      by_cases hodd : j % 2 = 1
      · have hnextEven : (j + 1) % 2 ≠ 1 := by omega
        rw [if_pos hodd, if_neg hnextEven, hindex]
        simp [CodeTag.Follows]
      · have hnextOdd : (j + 1) % 2 = 1 := by omega
        rw [if_neg hodd, if_pos hnextOdd, hindex]
        simp [CodeTag.Follows]
  · have hjnext : j + 1 ≠ 0 := by omega
    simp only [blockTag, if_neg hu]
    repeat' first | split
    all_goals simp_all [CodeTag.Follows, CodeTag.IsInBase]

private theorem blockTag_follows_nextRoot (beta : ℕ → Bool) (r : ℕ) :
    (blockTag beta r (2 * r)).Follows (blockTag beta (r + 1) 0) := by
  simp only [blockTag]
  repeat' first | split
  all_goals simp_all [CodeTag.Follows, CodeTag.IsInBase] <;> omega

private theorem blockTag_eq_k_index (beta : ℕ → Bool) {r j : ℕ}
    (h : blockTag beta r j = .k) : j = 0 := by
  simp only [blockTag] at h
  repeat' first | split at h
  all_goals simp_all

private theorem blockTag_eq_k_root (beta : ℕ → Bool) {r j : ℕ}
    (h : blockTag beta r j = .k) : 2 ≤ r := by
  simp only [blockTag] at h
  repeat' first | split at h
  all_goals simp_all <;> omega

private theorem blockTag_one_two_inBase (beta : ℕ → Bool) {r : ℕ}
    (_h : blockTag beta r 0 = .k) :
    (blockTag beta r 1).IsInBase ∧ (blockTag beta r 2).IsInBase := by
  by_cases hu : 3 ≤ r ∧ r % 3 = 0 <;>
    simp [blockTag, hu, CodeTag.IsInBase]

/-- Consecutive code tags follow one of the symbolic interval-cover edges from
[LY75, Appendix 2, pp. 991-992]. -/
theorem codeTag_follows (beta : ℕ → Bool) (n : ℕ) :
    (codeTag beta n).Follows (codeTag beta (n + 1)) := by
  let r := n.sqrt
  let j := n - r ^ 2
  have hrSq : r ^ 2 ≤ n := by simpa [r] using Nat.sqrt_le' n
  have hn : r ^ 2 + j = n := by
    simp only [j]
    exact Nat.add_sub_of_le hrSq
  have hsquare : (r + 1) ^ 2 = r ^ 2 + 2 * r + 1 := by ring
  have hj : j ≤ 2 * r := by
    have hlt := Nat.lt_succ_sqrt' n
    change n < (r + 1) ^ 2 at hlt
    rw [← hn, hsquare] at hlt
    omega
  have hcurrent : codeTag beta n = blockTag beta r j := by
    simp [codeTag, blockTag, r, j]
  by_cases hend : j = 2 * r
  · have hnnext : n + 1 = (r + 1) ^ 2 := by
      rw [← hn, hend, hsquare]
    have hsqrtNext : (n + 1).sqrt = r + 1 := by simp [hnnext]
    have hnext : codeTag beta (n + 1) = blockTag beta (r + 1) 0 := by
      have hdiff : n + 1 - (r + 1) ^ 2 = 0 := by simp [hnnext]
      unfold codeTag blockTag
      dsimp only
      rw [hsqrtNext, hdiff]
    rw [hcurrent, hnext]
    simpa [hend] using blockTag_follows_nextRoot beta r
  · have hjlt : j < 2 * r := lt_of_le_of_ne hj hend
    have hnnext : n + 1 = r ^ 2 + (j + 1) := by omega
    have hsqrtNext : (n + 1).sqrt = r := by
      rw [hnnext]
      apply Nat.sqrt_add_eq'
      omega
    have hnext : codeTag beta (n + 1) = blockTag beta r (j + 1) := by
      have hdiff : n + 1 - r ^ 2 = j + 1 := by omega
      unfold codeTag blockTag
      dsimp only
      rw [hsqrtNext, hdiff]
    rw [hcurrent, hnext]
    exact blockTag_follows_succ beta hjlt

/-- Each occurrence of `K` is followed by two tags interpreted inside the base
interval, the endpoint-exclusion pattern of [LY75, Appendix 2, p. 991]. -/
theorem codeTag_k_next_two_inBase (beta : ℕ → Bool) {n : ℕ}
    (hnK : codeTag beta n = .k) :
    (codeTag beta (n + 1)).IsInBase ∧
      (codeTag beta (n + 2)).IsInBase := by
  let r := n.sqrt
  let j := n - r ^ 2
  have hrSq : r ^ 2 ≤ n := by simpa [r] using Nat.sqrt_le' n
  have hn : r ^ 2 + j = n := by
    simp only [j]
    exact Nat.add_sub_of_le hrSq
  have hcurrent : codeTag beta n = blockTag beta r j := by
    simp [codeTag, blockTag, r, j]
  rw [hcurrent] at hnK
  have hj0 : j = 0 := blockTag_eq_k_index beta hnK
  have hr2 : 2 ≤ r := blockTag_eq_k_root beta hnK
  have hnSquare : n = r ^ 2 := by omega
  have hsqrt1 : (n + 1).sqrt = r := by
    rw [hnSquare]
    apply Nat.sqrt_add_eq'
    omega
  have hsqrt2 : (n + 2).sqrt = r := by
    rw [hnSquare]
    apply Nat.sqrt_add_eq'
    omega
  have htag1 : codeTag beta (n + 1) = blockTag beta r 1 := by
    have hdiff : n + 1 - r ^ 2 = 1 := by omega
    unfold codeTag blockTag
    dsimp only
    rw [hsqrt1, hdiff]
  have htag2 : codeTag beta (n + 2) = blockTag beta r 2 := by
    have hdiff : n + 2 - r ^ 2 = 2 := by omega
    unfold codeTag blockTag
    dsimp only
    rw [hsqrt2, hdiff]
  rw [htag1, htag2]
  exact blockTag_one_two_inBase beta (by simpa [hj0] using hnK)

/-- Every coordinate occurs at arbitrarily large encoding squares, replacing
the density-code recurrence in [LY75, Appendix 2, pp. 990-991]. -/
theorem frequently_encodingTime_of_bit (i : ℕ) :
    ∃ᶠ n in Filter.atTop,
      ∃ t : ℕ, n = encodingTime t ∧ (Nat.unpair t).1 = i := by
  refine Filter.frequently_atTop.2 fun N => ?_
  let t := Nat.pair i N
  have hNt : N ≤ t := Nat.right_le_pair i N
  have htRoot : t ≤ 3 * t + 2 := by omega
  have hRootSq : 3 * t + 2 ≤ (3 * t + 2) ^ 2 :=
    le_self_pow (by omega) (by decide)
  refine ⟨encodingTime t, hNt.trans (htRoot.trans hRootSq), t, rfl, ?_⟩
  simp [t]

/-- Universal blocks accommodating a fixed positive shift occur arbitrarily
late, supplying condition (B) from [LY75, Appendix 2, p. 991]. -/
theorem frequently_universalShiftTime {p : ℕ} (hp : 0 < p) :
    ∃ᶠ n in Filter.atTop,
      ∃ t : ℕ, n = universalTime t ∧
        p < 2 * universalRoot t + 1 := by
  refine Filter.frequently_atTop.2 fun N => ?_
  let t := N + p
  have hNt : N ≤ t := by simp [t]
  have htRoot : t ≤ universalRoot t := by simp [universalRoot]; omega
  have hRootSq : universalRoot t ≤ universalRoot t ^ 2 :=
    le_self_pow (by unfold universalRoot; omega) (by decide)
  refine ⟨universalTime t, hNt.trans (htRoot.trans hRootSq), t, rfl, ?_⟩
  simp [universalRoot]
  omega

/-- A positive shift that remains inside a universal block starts at `K` and
ends in a base-contained tag, for [LY75, Appendix 2, condition (B), p. 991]. -/
theorem codeTag_universalShift_inBase (beta : ℕ → Bool) (t : ℕ) {p : ℕ}
    (hp : 0 < p) (hpBound : p < 2 * universalRoot t + 1) :
    codeTag beta (universalTime t) = .k ∧
      (codeTag beta (universalTime t + p)).IsInBase := by
  refine ⟨codeTag_universalStart beta t, ?_⟩
  rw [codeTag_universalBridge beta t hp (by omega)]
  split <;> simp [CodeTag.IsInBase]

/-- The first step of every universal block enters the common lower bridge used
for [LY75, Appendix 2, equation (2.1), p. 992]. -/
theorem codeTag_universalFirstBridge (beta : ℕ → Bool) (t : ℕ) :
    codeTag beta (universalTime t + 1) =
      .lower (2 * universalRoot t - 1) := by
  simpa using codeTag_universalBridge beta t (j := 1) (by omega) (by
    simp [universalRoot]
    omega)

/-- Universal square times tend to infinity, as needed for the frequent common
blocks in [LY75, Appendix 2, pp. 991-992]. -/
theorem tendsto_universalTime :
    Filter.Tendsto universalTime Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.2 fun N => Filter.eventually_atTop.2 ⟨N, ?_⟩
  intro t ht
  have htRoot : t ≤ universalRoot t := by simp [universalRoot]; omega
  have hRootSq : universalRoot t ≤ universalRoot t ^ 2 :=
    le_self_pow (by unfold universalRoot; omega) (by decide)
  exact ht.trans (htRoot.trans hRootSq)

/-- The lower-bridge indices singled out by universal blocks tend to infinity,
as in the convergence argument of [LY75, Appendix 2, equation (2.1), p. 992]. -/
theorem tendsto_universalBridgeIndex :
    Filter.Tendsto (fun t => 2 * universalRoot t - 1)
      Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.2 fun N => Filter.eventually_atTop.2 ⟨N, ?_⟩
  intro t ht
  have : t ≤ 2 * universalRoot t - 1 := by
    simp [universalRoot]
    omega
  exact ht.trans this

end PeriodThree
