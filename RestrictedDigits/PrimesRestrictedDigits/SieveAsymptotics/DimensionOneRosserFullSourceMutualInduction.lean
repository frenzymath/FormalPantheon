import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserFullSourceReadyAssembly
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserFullSourceUpperSmallCoordinate
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSmallLogSourceAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceDirectTargets
import PrimesRestrictedDigits.SieveAsymptotics.RosserSourceRecurrence
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserLogTransform
/-! # DimensionOneRosserFullSourceMutualInduction -/

set_option maxHeartbeats 4000000

/-!
# Complete source targets by mutual carrier induction

The complete upper and lower Rosser source targets are proved simultaneously by strong
induction on the filtered prime-carrier length. The proof combines the bounded-log and direct
terminal branches with the ready ledgers and the low-coordinate upper closure. See
`IWANIEC-ROSSER-SIEVE-1980`, Eqs. (4.4)-- (4.6) and (8.7)--(8.14).
-/

namespace PrimesRestrictedDigits

private theorem fullSourceMutualInduction_eight_le_level
    {level : Real} (hlevel : 2 <= level)
    (hLExp : Real.exp 1 <= Real.log level)
    (hgate : 124800 + 14400 *
      Real.log (Real.log (Real.log level)) <=
        Real.log (Real.log level)) :
    8 <= level := by
  have hlevelPos : 0 < level := by linarith
  have hLPos : 0 < Real.log level :=
    (Real.exp_pos 1).trans_le hLExp
  have hlogLOne : 1 <= Real.log (Real.log level) :=
    (Real.le_log_iff_exp_le hLPos).2 hLExp
  have hlogLogNonneg :
      0 <= Real.log (Real.log (Real.log level)) :=
    Real.log_nonneg hlogLOne
  have hlogLLarge : 124800 <= Real.log (Real.log level) := by
    nlinarith
  have hlogLLe := Real.log_le_sub_one_of_pos hLPos
  have hlevelLe := Real.log_le_sub_one_of_pos hlevelPos
  nlinarith

private theorem fullSourceMutualInduction_baseCutoff_lt
    {level z s : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsUpper : s < 3) :
    iwaniecBaseCutoff level < z := by
  have hlevelPos : 0 < level := by linarith
  have hzPos : 0 < z := by linarith
  have hbasePos : 0 < iwaniecBaseCutoff level :=
    Real.rpow_pos_of_pos hlevelPos _
  apply (Real.log_lt_log_iff hbasePos hzPos).mp
  rw [log_iwaniecBaseCutoff hlevelPos]
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hratio : Real.log level / Real.log z < 3 := by
    rw [<- hs]
    exact hsUpper
  have hlog : Real.log level < 3 * Real.log z :=
    (div_lt_iff₀ hlogz).mp hratio
  linarith

/-- One absolute multiplier proves both complete raw source targets for every
finite decimal-admissible prime carrier and every state in the source domain.
-/
theorem exists_dimensionOneRosserFullSourceTargets :
    ∃ D : Real, 1 <= D ∧
      ∀ (P : Finset Nat),
        (∀ p, p ∈ P -> p.Prime) ->
        (∀ p, p ∈ P -> ¬p ∣ 10) ->
        (∀ {level z s : Real},
          2 <= level -> 2 <= z ->
          s = Real.log level / Real.log z -> 1 < s ->
          dimensionOneRosserFullSourceUpperTarget P D level z s) ∧
        (∀ {level z s : Real},
          2 <= level -> 2 <= z ->
          s = Real.log level / Real.log z -> 2 <= s ->
          dimensionOneRosserFullSourceLowerTarget P D level z s) := by
  obtain ⟨K, hK, hGlobalRatio⟩ := exists_decimalSieveDensityRatio_bound
  obtain ⟨c, hc, hmodelPlus, hmodelMinus⟩ :=
    exists_dimensionOneRosserModelRaw_le_delay_closed
  obtain ⟨Sdirect, hSdirect, hDirect⟩ :=
    exists_dimensionOneRosserSourceDirectTargets_ge
  obtain ⟨Splus, hSplus, hPlusLedger⟩ :=
    dimensionOneRosserPlusRawFullSourceLedger
  obtain ⟨Sminus, hSminus, hMinusLedger⟩ :=
    dimensionOneRosserMinusRawFullSourceLedger
  obtain ⟨Ssmall, hSsmall, hSmallUpper⟩ :=
    exists_dimensionOneRosserFullSourceUpperSmallCoordinateTarget
  let S : Real := max Sdirect (max Splus (max Sminus Ssmall))
  have hSdirectS : Sdirect <= S := by
    dsimp only [S]
    exact le_max_left _ _
  have hSplusS : Splus <= S := by
    dsimp only [S]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hSminusS : Sminus <= S := by
    dsimp only [S]
    exact (le_max_left _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  have hSsmallS : Ssmall <= S := by
    dsimp only [S]
    exact (le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  have hS : Real.exp 5000 + 1 <= S := hSdirect.trans hSdirectS
  have hKNonneg : 0 <= K := by linarith
  obtain ⟨Lambda0, hLambda0, hCutoff⟩ :=
    exists_dimensionOneRosserSourceCutoffData_threshold hKNonneg hS
  let Lambda : Real := max 8 Lambda0
  have hLambdaPos : 0 < Lambda := by
    exact (by norm_num : (0 : Real) < 8).trans_le (le_max_left _ _)
  have hLambda0Lambda : Lambda0 <= Lambda := by
    dsimp only [Lambda]
    exact le_max_right _ _
  let Dsmall : Real :=
    dimensionOneRosserSmallLogAbsorptionConstant Lambda
  let Dsource : Real := 2 * (1 + K) + 2304 * c * K
  let D : Real := max 1 (max Dsmall Dsource)
  have hD : 1 <= D := by
    dsimp only [D]
    exact le_max_left _ _
  have hDNonneg : 0 <= D := by linarith
  have hDsmall : Dsmall <= D := by
    dsimp only [D]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hDsource : 2 * (1 + K) + 2304 * c * K <= D := by
    dsimp only [Dsource, D]
    exact (le_max_right _ _).trans (le_max_right _ _)
  have hKPos : 0 < K := by linarith
  have hSmall :=
    dimensionOneRosserSmallLogSourceTargets Lambda hLambdaPos
  refine ⟨D, hD, ?_⟩
  intro P hprime hdecimal
  have hStrict : ∀ x y : Real, 2 <= x -> x < y ->
      sieveDensityBelow P (fun p => (p : Real)⁻¹) x /
          sieveDensityBelow P (fun p => (p : Real)⁻¹) y <
        (Real.log y / Real.log x) * (1 + K / Real.log x) :=
    fun x y hx hxy => hGlobalRatio P x y hprime hdecimal hx hxy
  let Claim : Nat -> Prop := fun n =>
    ∀ {level z s : Real},
      (sieveFactorsBelow P z).length = n ->
      2 <= level -> 2 <= z ->
      s = Real.log level / Real.log z ->
      (1 < s ->
        dimensionOneRosserFullSourceUpperTarget P D level z s) ∧
      (2 <= s ->
        dimensionOneRosserFullSourceLowerTarget P D level z s)
  have hClaim : ∀ n, Claim n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        dsimp only [Claim]
        intro level z s hlength hlevel hz hs
        constructor
        · intro hsOne
          by_cases hlogSmall : Real.log level <= Lambda
          · have hPartial := hSmall.1 P
                (sieveFactorsBelow P z).length hprime hlevel hz hs hsOne
                hlogSmall
            have hFull :=
              dimensionOneRosserFullSourceUpperTarget_of_sourceTarget_at_carrierLength
                P Dsmall hprime hsOne hPartial
            exact dimensionOneRosserFullSourceUpperTarget_mono_in_multiplier
              P hDsmall hprime hlevel hsOne hFull
          · have hlarge : Lambda0 <= Real.log level :=
              hLambda0Lambda.trans (le_of_lt (lt_of_not_ge hlogSmall))
            obtain ⟨data⟩ := hCutoff hlevel hlarge
            by_cases hdirect : data.s0 <= s
            · have hPair := hDirect P (sieveFactorsBelow P z).length
                  hD hprime hlevel hz hs
                  (hSdirectS.trans data.hsTail) hdirect data.hLExp
                  data.hsource
              exact
                dimensionOneRosserFullSourceUpperTarget_of_sourceTarget_at_carrierLength
                  P D hprime hsOne hPair.1
            · have hready : s < data.s0 := lt_of_not_ge hdirect
              by_cases hsThree : 3 <= s
              · have hRatio : ∀ u : Real,
                    level ^ (1 / data.s0) <= u -> u < z ->
                    sieveDensityBelow P (fun q => (q : Real)⁻¹) u /
                        sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
                      (Real.log z / Real.log u) *
                        (1 + K / Real.log u) := by
                    intro u hu huz
                    exact (hStrict u z (data.hcutoff.trans hu) huz).le
                have hledger := hPlusLedger P hc hD hDsource hmodelPlus
                  hmodelMinus hKNonneg hprime hlevel hz hs hsThree hready
                  data.hcutoff (hSplusS.trans data.hsTail) data.hsource
                  data.hLExp data.hgate data.hgrowth data.hsmall hRatio
                apply
                  dimensionOneRosserFullSourceUpperTarget_of_innerAndRawLedger
                    P D hDNonneg hprime hlevel hz hs hsThree hready
                      data.hcutoff _ hledger
                intro p hpP _hpCutoff hpz
                have hpPrime := hprime p hpP
                have hpTwo : (2 : Real) <= p := by
                  exact_mod_cast hpPrime.two_le
                have hpOne : (1 : Real) < p := by
                  exact_mod_cast hpPrime.one_lt
                have hdomains :=
                  iwaniecRosserEquation_four_five_innerDomains P
                    level z s hprime hlevel hz hs hsThree hpP hpz
                have hzSq : (2 : Real) <= z ^ 2 := by nlinarith
                have hinnerLevel : 2 <= level / (p : Real) :=
                  hzSq.trans hdomains.1.le
                have huEq : buchstabArgument level (p : Real) =
                    Real.log (level / (p : Real)) /
                      Real.log (p : Real) :=
                  (log_div_log_eq_buchstabArgument (by linarith) hpOne).symm
                have huTwo : 2 <= buchstabArgument level (p : Real) := by
                  rw [huEq]
                  exact hdomains.2.le
                have hlengthLt :=
                  sieveFactorsBelow_length_lt_of_mem_of_lt P hpP hpz
                rw [hlength] at hlengthLt
                have hIH :
                    Claim (sieveFactorsBelow P (p : Real)).length :=
                  ih _ hlengthLt
                dsimp only [Claim] at hIH
                have hTarget :=
                  (hIH (level := level / (p : Real)) (z := (p : Real))
                    (s := buchstabArgument level (p : Real)) rfl
                    hinnerLevel hpTwo huEq).2 huTwo
                unfold dimensionOneRosserFullSourceLowerTarget at hTarget
                exact hTarget.le
              · have hsUpper : s < 3 := lt_of_not_ge hsThree
                have hlevelEight : 8 <= level :=
                  fullSourceMutualInduction_eight_le_level hlevel
                    data.hLExp data.hgate
                have hbase : 2 <= iwaniecBaseCutoff level :=
                  two_le_iwaniecBaseCutoff_of_eight_le hlevelEight
                have hlevelPos : 0 < level := by linarith
                have hLPos : 0 < Real.log level :=
                  Real.log_pos (by linarith)
                have hbaseCoord : (3 : Real) = Real.log level /
                    Real.log (iwaniecBaseCutoff level) := by
                  rw [log_iwaniecBaseCutoff hlevelPos]
                  field_simp [hLPos.ne']
                have hbasez : iwaniecBaseCutoff level < z :=
                  fullSourceMutualInduction_baseCutoff_lt hlevel hz hs
                    hsUpper
                apply hSmallUpper P data hc hD hDsource hmodelPlus
                  hmodelMinus hKPos hprime hStrict hlevel hz hs hsOne
                    hsUpper (hSsmallS.trans data.hsTail)
                intro p hpP _hpCutoff hpbase
                have hpPrime := hprime p hpP
                have hpTwo : (2 : Real) <= p := by
                  exact_mod_cast hpPrime.two_le
                have hpOne : (1 : Real) < p := by
                  exact_mod_cast hpPrime.one_lt
                have hdomains :=
                  iwaniecRosserEquation_four_five_innerDomains P level
                    (iwaniecBaseCutoff level) 3 hprime hlevel hbase
                      hbaseCoord (by norm_num) hpP hpbase
                have hbaseSq : (2 : Real) <=
                    (iwaniecBaseCutoff level) ^ 2 := by nlinarith
                have hinnerLevel : 2 <= level / (p : Real) :=
                  hbaseSq.trans hdomains.1.le
                have huEq : buchstabArgument level (p : Real) =
                    Real.log (level / (p : Real)) /
                      Real.log (p : Real) :=
                  (log_div_log_eq_buchstabArgument hlevelPos hpOne).symm
                have huTwo : 2 <= buchstabArgument level (p : Real) := by
                  rw [huEq]
                  exact hdomains.2.le
                have hlengthLt :=
                  sieveFactorsBelow_length_lt_of_mem_of_lt P hpP
                    (hpbase.trans hbasez)
                rw [hlength] at hlengthLt
                have hIH :
                    Claim (sieveFactorsBelow P (p : Real)).length :=
                  ih _ hlengthLt
                dsimp only [Claim] at hIH
                exact (hIH (level := level / (p : Real))
                  (z := (p : Real))
                  (s := buchstabArgument level (p : Real)) rfl
                  hinnerLevel hpTwo huEq).2 huTwo
        · intro hsTwo
          by_cases hlogSmall : Real.log level <= Lambda
          · have hPartial := hSmall.2 P
                (sieveFactorsBelow P z).length hprime hlevel hz hs hsTwo
                hlogSmall
            have hFull :=
              dimensionOneRosserFullSourceLowerTarget_of_sourceTarget_at_carrierLength
                P Dsmall hprime hsTwo hPartial
            exact dimensionOneRosserFullSourceLowerTarget_mono_in_multiplier
              P hDsmall hprime hlevel hsTwo hFull
          · have hlarge : Lambda0 <= Real.log level :=
              hLambda0Lambda.trans (le_of_lt (lt_of_not_ge hlogSmall))
            obtain ⟨data⟩ := hCutoff hlevel hlarge
            by_cases hdirect : data.s0 <= s
            · have hPair := hDirect P (sieveFactorsBelow P z).length
                  hD hprime hlevel hz hs
                  (hSdirectS.trans data.hsTail) hdirect data.hLExp
                  data.hsource
              exact
                dimensionOneRosserFullSourceLowerTarget_of_sourceTarget_at_carrierLength
                  P D hprime hsTwo hPair.2
            · have hready : s < data.s0 := lt_of_not_ge hdirect
              have hRatio : ∀ u : Real,
                  level ^ (1 / data.s0) <= u -> u < z ->
                  sieveDensityBelow P (fun q => (q : Real)⁻¹) u /
                      sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
                    (Real.log z / Real.log u) *
                      (1 + K / Real.log u) := by
                intro u hu huz
                exact (hStrict u z (data.hcutoff.trans hu) huz).le
              have hledger := hMinusLedger P hc hD hDsource hmodelPlus
                hmodelMinus hKNonneg hprime hlevel hz hs hsTwo hready
                data.hcutoff (hSminusS.trans data.hsTail) data.hsource
                data.hLExp data.hgate data.hgrowth data.hsmall hRatio
              apply
                dimensionOneRosserFullSourceLowerTarget_of_innerAndRawLedger
                  P D hDNonneg hprime hlevel hz hs hsTwo hready data.hcutoff
                    _ hledger
              intro p hpP _hpCutoff hpz
              have hpPrime := hprime p hpP
              have hpTwo : (2 : Real) <= p := by
                exact_mod_cast hpPrime.two_le
              have hpOne : (1 : Real) < p := by
                exact_mod_cast hpPrime.one_lt
              have hdomains :=
                iwaniecRosserEquation_four_four_innerDomains P level z s
                  hprime hlevel hz hs hsTwo hpP hpz
              have hinnerLevel : 2 <= level / (p : Real) :=
                hz.trans hdomains.1.le
              have huEq : buchstabArgument level (p : Real) =
                  Real.log (level / (p : Real)) / Real.log (p : Real) :=
                (log_div_log_eq_buchstabArgument (by linarith) hpOne).symm
              have huOne : 1 < buchstabArgument level (p : Real) := by
                rw [huEq]
                exact hdomains.2
              have hlengthLt :=
                sieveFactorsBelow_length_lt_of_mem_of_lt P hpP hpz
              rw [hlength] at hlengthLt
              have hIH :
                  Claim (sieveFactorsBelow P (p : Real)).length :=
                ih _ hlengthLt
              dsimp only [Claim] at hIH
              have hTarget :=
                (hIH (level := level / (p : Real)) (z := (p : Real))
                  (s := buchstabArgument level (p : Real)) rfl
                  hinnerLevel hpTwo huEq).1 huOne
              unfold dimensionOneRosserFullSourceUpperTarget at hTarget
              exact hTarget.le
  constructor
  · intro level z s hlevel hz hs hsOne
    exact (hClaim (sieveFactorsBelow P z).length rfl hlevel hz hs).1 hsOne
  · intro level z s hlevel hz hs hsTwo
    exact (hClaim (sieveFactorsBelow P z).length rfl hlevel hz hs).2 hsTwo

end PrimesRestrictedDigits
