import MathlibNt.Wu2008DoubleSieve.TruncatedSixthSmallDeltaEndpoint
import MathlibNt.Wu2008DoubleSieve.ImprovementFamilies

namespace Wu2008DoubleSieve.BaseLowerCounts
open Finset Set Filter Real
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

/-- At unit divisibility the strict source carrier is the original carrier. -/
theorem source_count_one (N : ℕ) (z : ℝ) :
    sourceSieveCount N 1 N z = sieveCount N 1 N z := by
  unfold sourceSieveCount sieveCount
  rw [sourceSieveCarrier_of_dvd_modulus N (one_dvd N)]

/-- The empty tuple has product one and multiplicity one. -/
theorem phi_zero (N : ℕ) (δ s : ℝ) (W : Fin 0 → Finset ℕ) :
    wuBoxPhi N δ W s = (sieveCount N 1 N (wuLocalCutoff N δ 1 s) : ℝ) := by
  rw [wuBoxPhi_eq_tuple_sum]
  simp [Fintype.piFinset, source_count_one]

/-- The level parameter cancels exactly, not just asymptotically. -/
theorem cutoff_exact {N : ℕ} {δ κ : ℝ} (hN : 0 < N)
    (hδ : δ < 1/2) :
    wuLocalCutoff N δ 1 ((1/2-δ)/κ) = (N : ℝ)^κ := by
  unfold wuLocalCutoff
  simp only [Nat.cast_one, div_one]
  rw [← rpow_mul (by positivity)]
  congr 1
  have hc : (1/2 : ℝ)-δ ≠ 0 := ne_of_gt (by linarith)
  rw [one_div_div]
  exact mul_div_cancel₀ κ hc

/-- The original zero-depth source box supplies the actual baseline count. -/
theorem fixed_delta_li {δ κ η : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hs : 1 ≤ (1/2-δ)/κ) (hs10 : (1/2-δ)/κ ≤ 10)
    (hη : 0 < η) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (wuLowerCoefficient ((1/2-δ)/κ) - η) *
        (4 * logarithmicIntegral N * wuSingularSeries N / ((1/2-δ)*log N)) ≤
      (sieveCount N 1 N ((N : ℝ)^κ) : ℝ) := by
  obtain ⟨T, hT⟩ := wuEventualImprovements_neg_mem false 1 le_rfl hδ hδhi hs hs10 hη
  refine ⟨max 4 T, le_max_left _ _, ?_⟩
  intro N hN he
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hNT : T ≤ N := (le_max_right _ _).trans hN
  have h := hT N hNT hN4 he 0 (1 + log (N : ℝ)^(-4 : ℝ)) Fin.elim0
    (wuSourceBox_zero_depth 1 N δ hN4)
  change (wuLowerCoefficient ((1/2-δ)/κ) + -η) * _ ≤ _ at h
  rw [boxTheta_zero_depth, phi_zero, cutoff_exact (by omega) hδhi,
    log_rpow (by positivity : (0 : ℝ) < N)] at h
  simpa only [sub_eq_add_neg] using h

/-- Integrating from two preserves the coefficient one, with only a two-unit loss. -/
theorem trueLi_full_lower {N : ℕ} (hN : 4 ≤ N) :
    ((N : ℝ)-2)/log N ≤ logarithmicIntegral N := by
  have hli := box_trueLi_sub_lower (show (2 : ℝ) ≤ 2 by norm_num)
    (show (2 : ℝ) ≤ N by exact_mod_cast (show 2 ≤ N by omega))
  have hli2 : 0 ≤ logarithmicIntegral 2 :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 le_rfl (by norm_num)
  linarith

/-- This multiplication uses a nonnegative classical coefficient explicitly. -/
theorem normalized_li_lower {N : ℕ} {c b : ℝ} (hN : 4 ≤ N)
    (hc : 0 < c) (hb : 0 ≤ b) :
    (4*b/c)*(1-2/(N : ℝ))*wuSingularSeries N*N/log N^2 ≤
      b * (4*logarithmicIntegral N*wuSingularSeries N/(c*log N)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < log (N : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < N by omega))
  have hC := (wuSingularSeries_pos N (by omega)).le
  have h := mul_le_mul_of_nonneg_left (trueLi_full_lower hN)
    (show 0 ≤ b*4*wuSingularSeries N/(c*log N) by positivity)
  calc
    _ = b*4*wuSingularSeries N/(c*log N) * (((N : ℝ)-2)/log N) := by
      field_simp
    _ ≤ _ := h
    _ = _ := by ring

/-- Continuity is used only for the classical coefficient at the fixed positive argument. -/
theorem coefficient_continuous {κ : ℝ} (hκ : 0 < κ) :
    ContinuousAt (fun δ : ℝ => 4 * wuLowerCoefficient ((1/2-δ)/κ) / (1/2-δ)) 0 := by
  have ha : ContinuousAt wuLowerCoefficient ((1/2-0)/κ) :=
    continuousOn_wuLowerCoefficient.continuousAt
      (isOpen_Ioi.mem_nhds (by change 0 < (1/2-0)/κ; positivity))
  apply ContinuousAt.div
  · have hg : ContinuousAt (fun δ : ℝ => (1/2-δ)/κ) 0 := by fun_prop
    exact continuousAt_const.mul (ha.comp (f := fun δ : ℝ => (1/2-δ)/κ) hg)
  · fun_prop
  · norm_num

/-- Choose a genuinely positive delta and baseline error before the integer threshold. -/
theorem choose_parameters {κ ε : ℝ} (hκlo : 1/20 ≤ κ) (hκhi : κ ≤ 1/4)
    (hε : 0 < ε) :
    ∃ δ η : ℝ, 0 < δ ∧ δ ≤ 1/1000 ∧ 0 < η ∧
      1 ≤ (1/2-δ)/κ ∧ (1/2-δ)/κ ≤ 10 ∧
      8*wuLowerCoefficient (1/(2*κ))-ε/2 <
        4*(wuLowerCoefficient ((1/2-δ)/κ)-η)/(1/2-δ) := by
  have hκ : 0 < κ := by linarith
  obtain ⟨r, hr, hnear⟩ := Metric.continuousAt_iff.mp (coefficient_continuous hκ)
    (ε/4) (by positivity)
  let δ : ℝ := min (r/2) (1/1000)
  have hδ : 0 < δ := lt_min (half_pos hr) (by norm_num)
  have hδhi : δ ≤ 1/1000 := min_le_right _ _
  have hδr : δ < r := (min_le_left _ _).trans_lt (by linarith)
  have hc : 0 < (1/2 : ℝ)-δ := by linarith
  have hd : dist δ 0 < r := by simpa [Real.dist_eq, abs_of_pos hδ] using hδr
  have hn := hnear hd
  rw [Real.dist_eq, abs_lt] at hn
  simp only [sub_zero] at hn
  have hf : 8*wuLowerCoefficient (1/(2*κ))-ε/4 <
      4*wuLowerCoefficient ((1/2-δ)/κ)/(1/2-δ) := by
    have he : 4*wuLowerCoefficient ((1/2 : ℝ)/κ)/(1/2) =
        8*wuLowerCoefficient (1/(2*κ)) := by
      rw [show (1/2 : ℝ)/κ = 1/(2*κ) by ring]
      ring
    linarith [he]
  refine ⟨δ, ε*(1/2-δ)/16, hδ, hδhi, by positivity, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ hκ).mpr
    linarith
  · apply (div_le_iff₀ hκ).mpr
    linarith
  · have he : 4*(wuLowerCoefficient ((1/2-δ)/κ)-ε*(1/2-δ)/16)/(1/2-δ) =
        4*wuLowerCoefficient ((1/2-δ)/κ)/(1/2-δ)-ε/4 := by
      rw [mul_sub, sub_div]
      congr 1
      apply (div_eq_iff (ne_of_gt hc)).mpr
      ring
    rw [he]
    linarith

/-- The classical lower bound for each fixed cutoff exponent. No count or AP
hypothesis is supplied, and the integer threshold follows both real parameters. -/
theorem actual_count_lower {κ ε : ℝ} (hκlo : 1/20 ≤ κ) (hκhi : κ ≤ 1/4)
    (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (8*wuLowerCoefficient (1/(2*κ))-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (sieveCount N 1 N ((N : ℝ)^κ) : ℝ) := by
  by_cases hzero : 8*wuLowerCoefficient (1/(2*κ))-ε ≤ 0
  · refine ⟨4, le_rfl, ?_⟩
    intro N hN _he
    have hs : 0 ≤ wuSingularSeries N * N / log N^(2 : ℕ) :=
      truncatedSixthClosure_scale_nonneg hN
    have h := mul_nonpos_of_nonpos_of_nonneg hzero hs
    have hn : (0 : ℝ) ≤ sieveCount N 1 N ((N : ℝ)^κ) := by
      unfold sieveCount
      positivity
    have h' : (8*wuLowerCoefficient (1/(2*κ))-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤ 0 := by
      simpa only [mul_div_assoc, mul_assoc] using h
    exact h'.trans hn
  · have htarget : 0 < 8*wuLowerCoefficient (1/(2*κ))-ε := lt_of_not_ge hzero
    obtain ⟨δ, η, hδ, hδhi, hη, hs, hs10, hclose⟩ := choose_parameters hκlo hκhi hε
    have hc : 0 < (1/2 : ℝ)-δ := by linarith
    let b := wuLowerCoefficient ((1/2-δ)/κ)-η
    let B := 4*b/(1/2-δ)
    have hB : 0 < B := by dsimp [B, b]; linarith
    have hb : 0 ≤ b := by
      have h := (lt_div_iff₀ hc).mp hB
      nlinarith
    obtain ⟨T, hT4, hT⟩ := fixed_delta_li hδ (by linarith) hs hs10 hη
    obtain ⟨M, hM⟩ := exists_nat_ge (4*B/ε)
    refine ⟨max T M, hT4.trans (le_max_left _ _), ?_⟩
    intro N hN he
    have hNT : T ≤ N := (le_max_left _ _).trans hN
    have hN4 : 4 ≤ N := hT4.trans hNT
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hMN : (M : ℝ) ≤ N := by exact_mod_cast ((le_max_right T M).trans hN)
    have hbudget : 4*B ≤ (N : ℝ)*ε := (div_le_iff₀ hε).mp (hM.trans hMN)
    have hsmall : B*(2/(N : ℝ)) ≤ ε/2 := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hNr).mpr
      nlinarith
    have hcoef : 8*wuLowerCoefficient (1/(2*κ))-ε ≤ B*(1-2/(N : ℝ)) := by
      change 8*wuLowerCoefficient (1/(2*κ))-ε/2 < B at hclose
      nlinarith
    have hscale : 0 ≤ wuSingularSeries N * N / log N^(2 : ℕ) :=
      truncatedSixthClosure_scale_nonneg hN4
    have hmain := mul_le_mul_of_nonneg_right hcoef hscale
    have hmain' : (8*wuLowerCoefficient (1/(2*κ))-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        B*(1-2/(N : ℝ))*wuSingularSeries N*N/log N^(2 : ℕ) := by
      simpa only [mul_div_assoc, mul_assoc] using hmain
    exact hmain'.trans ((normalized_li_lower hN4 hc hb).trans (hT N hNT he))

end Wu2008DoubleSieve.BaseLowerCounts
