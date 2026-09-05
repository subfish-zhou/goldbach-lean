import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseI1423SigmaCubedDecay

open Filter Topology Asymptotics

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Case I: source-large-log uniform cutoff

The qualitative `(14.23)` scalar estimate was previously instantiated at fixed
`K`, so its eventual threshold could still depend on `K`.  The source has
already chosen `C1` before `K` and enters Case I only after
`C1 * K^Theta < log D`.  We spend the power `2 / Theta` to absorb the exact
`K^2` coefficient and apply the source-scalar estimate with the strengthened
exponent `Delta + 2 / Theta`.  Thus the cutoff below is chosen before
`K`, every depth and coordinate, and the later Claim-14.5 constant.
-/

/-- Quantitative replacement for the fixed-`K` eventuality hidden in the old
endpoint API.  The hypotheses are precisely the strict exponent margin needed
when the `K^2` in (14.23) is paid by `log D > C1*K^Theta`. -/
theorem exists_caseI1423_sourceScalar_sourceLargeLog_uniform
    {d Δ Θ : ℝ}
    (hΔ0 : 0 < Δ) (hΘ : 0 < Θ)
    (hmargin : Δ + 2 / Θ < 1)
    (hd : 7 / (1 - (Δ + 2 / Θ)) < d) :
    ∃ C1min : ℝ, 1 ≤ C1min ∧
      ∀ (C1 K D : ℝ), C1min ≤ C1 → 2 ≤ K → 2 ≤ D →
        C1 * K ^ Θ < Real.log D →
        K ^ 2 * sourceSigma D d ^ 3 *
            Real.log (Real.exp 1 * sourceSigma D d) *
            Real.log (Real.log D) /
            (Real.log D) ^ (1 - Δ) ≤ 1 := by
  let η : ℝ := 2 / Θ
  let Δ' : ℝ := Δ + η
  have hη0 : 0 < η := by dsimp [η]; positivity
  have hΔ'0 : 0 < Δ' := by dsimp [Δ']; linarith
  have hΔ'1 : Δ' < 1 := by simpa [Δ', η] using hmargin
  have hd' : 7 / (1 - Δ') < d := by simpa [Δ', η] using hd
  have hbaseEv :=
    (tendsto_caseI1423_sourceScalar 1 d Δ' hΔ'0 hΔ'1 hd').eventually
      (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))
  have hev : ∀ᶠ D : ℝ in atTop,
      1 ^ 2 * sourceSigma D d ^ 3 *
          Real.log (Real.exp 1 * sourceSigma D d) *
          Real.log (Real.log D) /
          (Real.log D) ^ (1 - Δ') ≤ 1 ∧
        Real.exp (Real.exp 1) ≤ D :=
    hbaseEv.and (eventually_ge_atTop (Real.exp (Real.exp 1)))
  obtain ⟨Dpre, hpre⟩ := eventually_atTop.1 hev
  let Dcut : ℝ := max Dpre (Real.exp (Real.exp 1))
  let C1min : ℝ := max 1 (Real.log Dcut)
  have hDcut0 : 0 < Dcut :=
    (Real.exp_pos (Real.exp 1)).trans_le (le_max_right _ _)
  have hC1min1 : 1 ≤ C1min := le_max_left _ _
  refine ⟨C1min, hC1min1, ?_⟩
  intro C1 K X hC1 hK hX2 hlarge
  have hK0 : 0 < K := by linarith
  have hKpow1 : 1 ≤ K ^ Θ := Real.one_le_rpow (by linarith) hΘ.le
  have hC11 : 1 ≤ C1 := hC1min1.trans hC1
  have hbudget : C1min ≤ C1 * K ^ Θ := by
    calc
      C1min ≤ C1 := hC1
      _ = C1 * 1 := by ring
      _ ≤ C1 * K ^ Θ := mul_le_mul_of_nonneg_left hKpow1 (by linarith)
  have hlogcut : Real.log Dcut < Real.log X :=
    (le_max_right 1 (Real.log Dcut)).trans_lt (hbudget.trans_lt hlarge)
  have hX0 : 0 < X := by linarith
  have hDX : Dcut < X := by
    have he := Real.exp_lt_exp.mpr hlogcut
    rw [Real.exp_log hDcut0, Real.exp_log hX0] at he
    exact he
  have hpreX := hpre X ((le_max_left Dpre (Real.exp (Real.exp 1))).trans hDX.le)
  have hbaseX := hpreX.1
  have hx1 : 1 < Real.log X := by
    have hlogcut1 : Real.exp 1 ≤ Real.log Dcut := by
      dsimp [Dcut]
      have hm := Real.strictMonoOn_log.monotoneOn
        (Real.exp_pos (Real.exp 1)) hDcut0
        (le_max_right Dpre (Real.exp (Real.exp 1)))
      simpa using hm
    exact (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le
      (hlogcut1.trans hlogcut.le)
  have hx0 : 0 < Real.log X := zero_lt_one.trans hx1
  have hKpowx : K ^ Θ ≤ Real.log X := by
    calc
      K ^ Θ = 1 * K ^ Θ := by ring
      _ ≤ C1 * K ^ Θ := mul_le_mul_of_nonneg_right hC11
        (Real.rpow_nonneg hK0.le Θ)
      _ ≤ Real.log X := hlarge.le
  have hK2 : K ^ 2 ≤ (Real.log X) ^ η := by
    have hp := Real.rpow_le_rpow (Real.rpow_nonneg hK0.le Θ)
      hKpowx hη0.le
    have hleft : (K ^ Θ) ^ η = K ^ 2 := by
      rw [← Real.rpow_mul hK0.le]
      have hΘne : Θ ≠ 0 := ne_of_gt hΘ
      rw [show Θ * η = 2 by dsimp [η]; field_simp]
      exact Real.rpow_two K
    rw [hleft] at hp
    exact hp
  have hd0 : 0 < d := by
    have hden : 0 < 1 - (Δ + 2 / Θ) := sub_pos.mpr hmargin
    have : 0 < 7 / (1 - (Δ + 2 / Θ)) := div_pos (by norm_num) hden
    linarith
  have hlog27 : 1 < Real.log (27 * X) := by
    apply (Real.lt_log_iff_exp_lt (by positivity : 0 < 27 * X)).2
    have hX1 : 1 < X := by linarith
    nlinarith [Real.exp_one_lt_d9]
  have hσ0 : 0 < sourceSigma X d := by
    unfold sourceSigma
    exact mul_pos (Real.rpow_pos_of_pos hx0 _) (Real.log_pos hlog27)
  have hlogs0 : 0 ≤ Real.log (Real.exp 1 * sourceSigma X d) := by
    apply Real.log_nonneg
    have hs1 : 1 ≤ sourceSigma X d := by
      unfold sourceSigma
      have hfirst : 1 ≤ (Real.log X) ^ (1 / d) :=
        Real.one_le_rpow hx1.le (one_div_nonneg.mpr hd0.le)
      have hsecond : 1 ≤ Real.log (Real.log (27 * X)) := by
        have hinner : Real.exp 1 ≤ Real.log (27 * X) := by
          have hcut : Real.exp 1 ≤ Real.log Dcut := by
            dsimp [Dcut]
            have hm := Real.strictMonoOn_log.monotoneOn
              (Real.exp_pos (Real.exp 1)) hDcut0
              (le_max_right Dpre (Real.exp (Real.exp 1)))
            simpa using hm
          have hDX' : Dcut ≤ 27 * X := by nlinarith
          exact hcut.trans (Real.strictMonoOn_log.monotoneOn hDcut0
            (mul_pos (by norm_num) hX0) hDX')
        exact (Real.le_log_iff_exp_le (by linarith [hlog27] :
          0 < Real.log (27 * X))).2 hinner
      nlinarith [mul_le_mul hfirst hsecond zero_le_one
        (Real.rpow_nonneg hx0.le (1 / d))]
    have : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    nlinarith [mul_le_mul this hs1 zero_le_one (Real.exp_pos 1).le]
  have hll0 : 0 ≤ Real.log (Real.log X) := Real.log_nonneg hx1.le
  have hrest0 : 0 ≤ sourceSigma X d ^ 3 *
      Real.log (Real.exp 1 * sourceSigma X d) * Real.log (Real.log X) := by
    positivity
  have hpowη0 : 0 < (Real.log X) ^ η := Real.rpow_pos_of_pos hx0 η
  have hpowrest : 0 < (Real.log X) ^ (1 - Δ - η) :=
    Real.rpow_pos_of_pos hx0 _
  have hbase' :
      sourceSigma X d ^ 3 * Real.log (Real.exp 1 * sourceSigma X d) *
          Real.log (Real.log X) /
          (Real.log X) ^ (1 - Δ - η) ≤ 1 := by
    have hexp : 1 - Δ' = 1 - Δ - η := by dsimp [Δ']; ring
    simpa only [one_pow, one_mul, hexp] using hbaseX
  have hrest : sourceSigma X d ^ 3 *
      Real.log (Real.exp 1 * sourceSigma X d) * Real.log (Real.log X) ≤
      (Real.log X) ^ (1 - Δ - η) :=
    (div_le_one hpowrest).mp hbase'
  have hnum : K ^ 2 * (sourceSigma X d ^ 3 *
      Real.log (Real.exp 1 * sourceSigma X d) * Real.log (Real.log X)) ≤
      (Real.log X) ^ η * (Real.log X) ^ (1 - Δ - η) :=
    mul_le_mul hK2 hrest hrest0 (Real.rpow_nonneg hx0.le η)
  have hpows : (Real.log X) ^ η * (Real.log X) ^ (1 - Δ - η) =
      (Real.log X) ^ (1 - Δ) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  apply (div_le_one (Real.rpow_pos_of_pos hx0 (1 - Δ))).2
  rw [← hpows]
  simpa only [mul_assoc] using hnum


end MathlibNt.SieveTheory
