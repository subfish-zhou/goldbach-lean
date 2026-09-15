import MathlibNt.Wu2008DoubleSieve.HighSixPrimeDeltaLimit

namespace Wu2008DoubleSieve.HighSixDeltaLimit
open Real Set Filter SingleUpperClassicalLimit
open scoped Topology

noncomputable def localGain (δ : ℝ) : ℝ :=
  4*firstFunctionalGainPsi δ HighSix.s HighSix.S*HighSix.primeIntegral δ
noncomputable def localGainOne : ℝ :=
  4*firstFunctionalGainPsiOne HighSix.s HighSix.S*HighSix.primeIntegral 0
noncomputable def sourcePenalty (δ : ℝ) : ℝ :=
  4*(2*δ/(1-2*δ))*omega3XIntegralEnvelope HighSix.s HighSix.S*HighSix.primeIntegral δ
noncomputable def limitCoefficient : ℝ :=
  TruncatedElevenClassicalCountLower.classicalCoefficient+localGainOne

/-- This fixed-delta penalty vanishes by changing delta, not by increasing N. -/
theorem penalty_factor_right_limit :
    Tendsto (fun δ : ℝ => 2*δ/(1-2*δ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hc : ContinuousAt (fun δ : ℝ => 2*δ/(1-2*δ)) 0 :=
    (by fun_prop : ContinuousAt (fun δ : ℝ => 2*δ) 0).div
      (by fun_prop) (by norm_num)
  have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simpa only [mul_zero, sub_zero, zero_div] using h

 theorem sourcePenalty_right_limit :
    Tendsto sourcePenalty (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := ((penalty_factor_right_limit.const_mul 4).mul_const
    (omega3XIntegralEnvelope HighSix.s HighSix.S)).mul primeIntegral_right_limit
  change Tendsto (fun δ => 4*(2*δ/(1-2*δ))*omega3XIntegralEnvelope HighSix.s HighSix.S*
    HighSix.primeIntegral δ) (𝓝[>] (0 : ℝ)) (𝓝 0)
  simpa only [mul_zero, zero_mul] using h

 theorem sourcePenalty_close {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ ∀ δ : ℝ, 0 < δ → δ < a → |sourcePenalty δ| < ε := by
  obtain ⟨a, ha, hb⟩ := Metric.tendsto_nhdsWithin_nhds.mp sourcePenalty_right_limit ε hε
  refine ⟨a, ha, ?_⟩
  intro δ hδ hδa
  simpa only [Real.dist_eq, sub_zero] using
    hb hδ (by simpa only [Real.dist_eq, sub_zero, abs_of_pos hδ] using hδa)

/-- The two absolute budgets work for either sign of PsiOne and the X envelope. -/
theorem localGain_abs_budget {δ : ℝ} (hδhi : δ ≤ 1/100) :
    |localGain δ-localGainOne| ≤
      4*|firstFunctionalGainPsiOne HighSix.s HighSix.S| *
        |HighSix.primeIntegral δ-HighSix.primeIntegral 0| + |sourcePenalty δ| := by
  have he : localGain δ-localGainOne =
      (4*firstFunctionalGainPsiOne HighSix.s HighSix.S)*
        (HighSix.primeIntegral δ-HighSix.primeIntegral 0)-sourcePenalty δ := by
    unfold localGain localGainOne sourcePenalty
    rw [HighSix.psi_source_penalty hδhi]
    ring
  rw [he]
  calc
    _ ≤ |(4*firstFunctionalGainPsiOne HighSix.s HighSix.S)*
        (HighSix.primeIntegral δ-HighSix.primeIntegral 0)|+|sourcePenalty δ| := abs_sub _ _
    _ = _ := by rw [abs_mul, abs_mul]; norm_num

 theorem localGain_close {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1/100 ∧ ∀ δ : ℝ,
      0 < δ → δ < a → |localGain δ-localGainOne| < ε := by
  let η := ε/(8*(|firstFunctionalGainPsiOne HighSix.s HighSix.S|+1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨a, ha, ha1, hA⟩ := primeIntegral_close hη
  obtain ⟨b, hb, hB⟩ := sourcePenalty_close (half_pos hε)
  refine ⟨min a b, lt_min ha hb, (min_le_left _ _).trans ha1, ?_⟩
  intro δ hδ hδab
  have hδa := hδab.trans_le (min_le_left a b)
  have hδb := hδab.trans_le (min_le_right a b)
  have hp := hA δ hδ hδa
  have hq := hB δ hδ hδb
  have hηeq : 8*(|firstFunctionalGainPsiOne HighSix.s HighSix.S|+1)*η = ε := by
    dsimp [η]; field_simp
  have hpay := mul_le_mul_of_nonneg_left hp.le
    (show 0 ≤ 4*|firstFunctionalGainPsiOne HighSix.s HighSix.S| by positivity)
  have hbudget := localGain_abs_budget (hδa.le.trans ha1)
  nlinarith only [hbudget, hpay, hq, hηeq, hη.le]

/-- The original complete K is retained literally. -/
theorem coefficient_difference (δ : ℝ) :
    HighSixPsiMother.psiCoefficient δ-limitCoefficient =
      -(Gdelta δ (1/3)-Glin (1/3))-
      (Gdelta δ truncatedSixthLowerSigma-Glin truncatedSixthLowerSigma)+
      (localGain δ-localGainOne) := by
  unfold HighSixPsiMother.psiCoefficient limitCoefficient
    TruncatedElevenClassicalCountLower.classicalCoefficient localGain
  ring

 theorem coefficient_close {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1/100 ∧ ∀ δ : ℝ,
      0 < δ → δ < a → |HighSixPsiMother.psiCoefficient δ-limitCoefficient| < ε := by
  have he : 0 < ε/3 := by positivity
  obtain ⟨a, ha, ha1, hA⟩ := Gdelta_close
    (by norm_num [truncatedSixthLowerAlpha] : truncatedSixthLowerAlpha ≤ (1/3 : ℝ)) le_rfl he
  obtain ⟨b, hb, _, hB⟩ := Gdelta_close
    (by norm_num [truncatedSixthLowerAlpha, truncatedSixthLowerSigma] :
      truncatedSixthLowerAlpha ≤ truncatedSixthLowerSigma)
    (by norm_num [truncatedSixthLowerSigma, truncatedSixthLowerAlpha] : truncatedSixthLowerSigma ≤ (1/3 : ℝ)) he
  obtain ⟨c, hc, _, hC⟩ := localGain_close he
  refine ⟨min a (min b c), lt_min ha (lt_min hb hc), (min_le_left _ _).trans ha1, ?_⟩
  intro δ hδ hδabc
  have hδa := hδabc.trans_le (min_le_left a (min b c))
  have hδbc := hδabc.trans_le (min_le_right a (min b c))
  have h1 := hA δ hδ hδa
  have h2 := hB δ hδ (hδbc.trans_le (min_le_left b c))
  have h3 := hC δ hδ (hδbc.trans_le (min_le_right b c))
  rw [coefficient_difference]
  apply lt_of_le_of_lt (abs_add_le _ _)
  have hsub := abs_sub (-(Gdelta δ (1/3)-Glin (1/3)))
    (Gdelta δ truncatedSixthLowerSigma-Glin truncatedSixthLowerSigma)
  rw [abs_neg] at hsub
  linarith only [hsub, h1, h2, h3]

 theorem coefficient_right_limit :
    Tendsto HighSixPsiMother.psiCoefficient (𝓝[>] (0 : ℝ)) (𝓝 limitCoefficient) := by
  apply Metric.tendsto_nhdsWithin_nhds.mpr
  intro ε hε
  obtain ⟨a, ha, _, h⟩ := coefficient_close hε
  refine ⟨a, ha, ?_⟩
  intro δ hδ hd
  change 0 < δ at hδ
  apply h δ hδ
  simpa only [Real.dist_eq, sub_zero, abs_of_pos hδ] using hd

/-- A positive delta is chosen for the error before any arithmetic threshold. -/
theorem choose_delta {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100 ∧
      limitCoefficient-ε < HighSixPsiMother.psiCoefficient δ := by
  obtain ⟨a, ha, ha1, h⟩ := coefficient_close hε
  refine ⟨a/2, half_pos ha, (half_le_self ha.le).trans ha1, ?_⟩
  have hh := (abs_lt.mp (h (a/2) (half_pos ha) (half_lt_self ha))).1
  linarith only [hh]

end Wu2008DoubleSieve.HighSixDeltaLimit
