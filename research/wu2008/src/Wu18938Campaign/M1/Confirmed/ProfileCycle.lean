import Wu18938Campaign.M1.Confirmed.ProfileActualExtension

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.FiniteProfile

open Wu2008DoubleSieve Rebox Real MeasureTheory NodeExtension Filter
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open scoped Classical Interval Topology

theorem cycle_integral {H : ℝ → ℝ} (hH : Antitone H) (c : ℝ) :
    profileIntegral (upperExtension H c) 4 6 =
      wuLowerCoefficient 6 - wuLowerCoefficient 4 -
        (D0 * c + (1 - D0) * aProfile H) := by
  have hsource := sigma_feedback (profile_div_integrable hH.intervalIntegrable)
  have hconst := (sigma_integrable (a := 3) (b := 5) (c := 4)
    (by norm_num) (by norm_num) (by norm_num)).const_mul c
  have hkernel : IntervalIntegrable (fun v => tailGain H c v / v) volume 3 5 := by
    convert hconst.add hsource.1 using 1
    funext v
    dsimp [tailGain]
    ring
  have hscalar : (∫ v in (3 : ℝ)..5, tailGain H c v / v) =
      D0 * c + (1 - D0) * aProfile H := by
    have heq : (fun v => tailGain H c v / v) =
        (fun v => c * (log (4 / (v - 1)) / v) +
          (∫ t in (v - 2)..3, H t / t * log ((t + 1) / (v - 1))) / v) := by
      funext v
      dsimp [tailGain]
      ring
    rw [heq,intervalIntegral.integral_add hconst hsource.1,
      intervalIntegral.integral_const_mul,hsource.2]
    have ha := (eq_div_iff (sub_pos.mpr D0_lt_one).ne').mp (aProfile_eq H)
    change c * D0 + _ = _
    nlinarith only [ha]
  have hclass := wuLowerCoefficient_sub_eq_integral (s := 4) (s' := 6) (by norm_num) (by norm_num)
  norm_num only [show (4 : ℝ) - 1 = 3 by norm_num,show (6 : ℝ) - 1 = 5 by norm_num] at hclass
  have hupper := wuUpperCoefficient_div_intervalIntegrable (a := 3) (b := 5) (by norm_num) (by norm_num)
  have heq : profileIntegral (upperExtension H c) 4 6 =
      (∫ v in (3 : ℝ)..5, wuUpperCoefficient v / v) -
        (∫ v in (3 : ℝ)..5, tailGain H c v / v) := by
    rw [← intervalIntegral.integral_sub hupper hkernel]
    unfold profileIntegral
    norm_num only [show (4 : ℝ) - 1 = 3 by norm_num,show (6 : ℝ) - 1 = 5 by norm_num]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 5)] at hv
    dsimp only
    rw [upperExtension_eq hH hv.1 hv.2]
    dsimp [tailGain]
    ring
  rw [heq,← hclass,hscalar]

theorem cycle_four_actual {H : ℝ → ℝ} (hH : Antitone H)
    (hb : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1 / 16)
    {δ c : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hc4 : c ≤ 1 / 4)
    (hHnode : UpperNodes δ (fun v => 1 - H v) 3) (hcnode : FourNode δ c) :
    FourNode δ (D0 * c + (1 - D0) * aProfile H) := by
  have hb1 : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1 :=
    fun v hv => ⟨(hb v hv).1,(hb v hv).2.trans (by norm_num)⟩
  have hfnode := lower_extension_actual hH hb1 hδ hHnode hcnode
  have hunode := upper_extension_actual hH hb1 hδ hc hc4 hfnode
  intro m η ε hη he
  obtain ⟨T0,hT04,h0⟩ := lower_buchstab_actual (upperExtension H c) 5
    ((upperExtension_mono hH hb1 hc).monotoneOn _)
    (fun v _ => upperExtension_bounds hH hb hc hc4 v)
    m hη hδ (half_pos he)
    (fun ρ hρ => hunode (m + 1) (η / 20) ρ (by positivity) hρ)
  obtain ⟨T1,_,h1⟩ := roughBox_lower_leaf_bounded m hη hδ (half_pos he)
  refine ⟨max T0 T1,hT04.trans (le_max_left _ _),?_⟩
  intro N hN heven i Δ V hbox
  have hbase := h1 N (by omega) heven i Δ V hbox 6 (by norm_num) (by norm_num)
  have htrans := h0 N (by omega) heven i Δ V hbox 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [cycle_integral hH] at htrans
  have ha : wuLowerCoefficient 4 = log 3 := by
    change 4 * jr1965f 4 / (2 * exp eulerMascheroniConstant) = log 3
    convert jr1965f_normalized_firstInterval (s := 4) (by norm_num) le_rfl using 1
    norm_num
  rw [ha] at htrans
  nlinarith only [hbase,htrans]

def cycleValue (H : ℝ → ℝ) (n : ℕ) : ℝ := aProfile H * (1 - D0 ^ n)

theorem cycleValue_zero (H : ℝ → ℝ) : cycleValue H 0 = 0 := by simp [cycleValue]

theorem cycleValue_succ (H : ℝ → ℝ) (n : ℕ) :
    cycleValue H (n + 1) = D0 * cycleValue H n + (1 - D0) * aProfile H := by
  simp only [cycleValue,pow_succ]
  ring

theorem cycleValue_bounds {H : ℝ → ℝ} (hH : Antitone H)
    (hb : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1 / 16) (n : ℕ) :
    0 ≤ cycleValue H n ∧ cycleValue H n ≤ 1 / 4 := by
  have ha := aProfile_bounds hH hb
  have hp := pow_le_one₀ D0_bounds.1 D0_lt_one.le (n := n)
  have hp0 := pow_nonneg D0_bounds.1 n
  dsimp [cycleValue]
  exact ⟨mul_nonneg ha.1 (by linarith),(mul_le_mul_of_nonneg_left
    (by linarith : 1 - D0 ^ n ≤ 1) ha.1).trans (by simpa using ha.2)⟩

theorem finite_cycle_four {H : ℝ → ℝ} (hH : Antitone H)
    (hb : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1 / 16)
    {δ : ℝ} (hδ : 0 < δ) (hHnode : UpperNodes δ (fun v => 1 - H v) 3) (n : ℕ) :
    FourNode δ (cycleValue H n) := by
  induction n with
  | zero => rw [cycleValue_zero]; exact fourNode_zero hδ
  | succ n ih =>
    rw [cycleValue_succ]
    exact cycle_four_actual hH hb hδ (cycleValue_bounds hH hb n).1
      (cycleValue_bounds hH hb n).2 hHnode ih

theorem cycleValue_tendsto (H : ℝ → ℝ) :
    Tendsto (cycleValue H) atTop (𝓝 (aProfile H)) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one D0_bounds.1 D0_lt_one
  change Tendsto (fun n => aProfile H * (1 - D0 ^ n)) atTop (𝓝 (aProfile H))
  simpa only [sub_zero,mul_one] using
    ((tendsto_const_nhds (x := (1 : ℝ))).sub hp).const_mul (aProfile H)

theorem fourNode_profile {H : ℝ → ℝ} (hH : Antitone H)
    (hb : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1 / 16)
    {δ : ℝ} (hδ : 0 < δ) (hHnode : UpperNodes δ (fun v => 1 - H v) 3) :
    FourNode δ (aProfile H) := by
  intro m η ε hη he
  obtain ⟨n,hn⟩ := ((tendsto_order.1 (cycleValue_tendsto H)).1
    (aProfile H - ε / 2) (by linarith)).exists
  obtain ⟨T,hT4,hT⟩ := finite_cycle_four hH hb hδ hHnode n m η (ε / 2) hη (half_pos he)
  refine ⟨T,hT4,?_⟩
  intro N hN heven i Δ V hbox
  have hpay := mul_le_mul_of_nonneg_right
    (show log 3 + aProfile H - ε ≤ log 3 + cycleValue H n - ε / 2 by linarith)
    (theta_nonneg hbox (hT4.trans hN) hη hδ)
  exact hpay.trans (hT N hN heven i Δ V hbox)

theorem full_extensions_actual {H : ℝ → ℝ} (hH : Antitone H)
    (hb : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1 / 16)
    {δ : ℝ} (hδ : 0 < δ) (hHnode : UpperNodes δ (fun v => 1 - H v) 3) :
    LowerNodes δ (lowerExtension H (aProfile H)) ∧
      UpperNodes δ (upperExtension H (aProfile H)) 5 := by
  have hb1 : ∀ v ∈ Set.Icc (1 : ℝ) 3, 0 ≤ H v ∧ H v ≤ 1 :=
    fun v hv => ⟨(hb v hv).1,(hb v hv).2.trans (by norm_num)⟩
  have hf := lower_extension_actual hH hb1 hδ hHnode (fourNode_profile hH hb hδ hHnode)
  exact ⟨hf,upper_extension_actual hH hb1 hδ (aProfile_bounds hH hb).1
    (aProfile_bounds hH hb).2 hf⟩

end Wu18938Campaign.M1.Confirmed.FiniteProfile
